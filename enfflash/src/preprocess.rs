/// Preprocessor: extracts Python function bodies from source before LALRPOP parsing.
///
/// Transforms:
///   fun name(x: int, y: str) : int { ... python code ... }
/// Into:
///   fun name(x: int, y: str) : int { "__PYBODY_0__" }
///
/// Returns (transformed source, vec of extracted bodies).

fn is_ident_byte(b: u8) -> bool {
    b.is_ascii_alphanumeric() || b == b'_'
}

pub fn preprocess_fun_bodies(src: &str) -> (String, Vec<String>) {
    let mut result = String::with_capacity(src.len());
    let mut bodies: Vec<String> = Vec::new();
    let bytes = src.as_bytes();
    let len = bytes.len();
    let mut i = 0;

    while i < len {
        // Look for a `fun ` or `tfun ` keyword at a word boundary (so the `fun`
        // inside `tfun` is not matched twice).  Both bodies are extracted the
        // same way and share the placeholder namespace.
        let prev_is_ident = i > 0 && is_ident_byte(bytes[i - 1]);
        let kw_len =
            if !prev_is_ident && i + 7 <= len && &bytes[i..i + 7] == b"pyinit " { Some(7) }
            else if !prev_is_ident && i + 5 <= len && &bytes[i..i + 5] == b"tfun " { Some(5) }
            else if !prev_is_ident && i + 4 <= len && &bytes[i..i + 4] == b"fun " { Some(4) }
            else { None };
        if let Some(kwl) = kw_len {
            let fun_start = i;
            // Find the opening '{' for the body
            let mut brace_pos = None;
            let mut j = i + kwl;
            while j < len {
                if bytes[j] == b'{' {
                    brace_pos = Some(j);
                    break;
                }
                j += 1;
            }
            if let Some(open) = brace_pos {
                // Write everything up to and including '{'
                result.push_str(&src[fun_start..=open]);

                // Now find the matching closing '}'
                let mut depth = 1u32;
                let mut k = open + 1;
                while k < len && depth > 0 {
                    if bytes[k] == b'{' {
                        depth += 1;
                    } else if bytes[k] == b'}' {
                        depth -= 1;
                    }
                    k += 1;
                }
                // k now points past the closing '}'
                let body = &src[open + 1..k - 1];
                let idx = bodies.len();
                bodies.push(body.to_string());

                result.push_str(&format!(" \"__PYBODY_{}__\" ", idx));
                result.push('}');
                i = k;
            } else {
                result.push(src[i..].chars().next().unwrap());
                i += src[i..].chars().next().unwrap().len_utf8();
            }
        } else {
            let ch = src[i..].chars().next().unwrap();
            result.push(ch);
            i += ch.len_utf8();
        }
    }

    (result, bodies)
}

/// After parsing, replace placeholder strings in FunDecl / TfunDecl bodies with
/// the actual Python code.
pub fn restore_fun_bodies(program: &mut crate::ast::Program, bodies: &[String]) {
    let restore = |body: &mut String| {
        if body.starts_with("__PYBODY_") && body.ends_with("__") {
            let idx_str = &body[9..body.len() - 2];
            if let Ok(idx) = idx_str.parse::<usize>() {
                if idx < bodies.len() {
                    *body = dedent(&bodies[idx]);
                }
            }
        }
    };
    for fd in &mut program.fun_decls {
        restore(&mut fd.body);
    }
    for td in &mut program.tfun_decls {
        restore(&mut td.body);
    }
    restore(&mut program.py_preamble);
}

/// Remove common leading whitespace from all non-empty lines (like Python's textwrap.dedent).
/// Also strips leading and trailing blank lines.
fn dedent(s: &str) -> String {
    let lines: Vec<&str> = s.lines().collect();
    // Find minimum indentation among non-empty lines
    let min_indent = lines.iter()
        .filter(|l| !l.trim().is_empty())
        .map(|l| l.len() - l.trim_start().len())
        .min()
        .unwrap_or(0);
    let dedented: Vec<&str> = lines.iter()
        .map(|l| {
            if l.trim().is_empty() {
                ""
            } else if l.len() >= min_indent {
                &l[min_indent..]
            } else {
                l.trim()
            }
        })
        .collect();
    // Trim leading and trailing empty lines
    let start = dedented.iter().position(|l| !l.is_empty()).unwrap_or(0);
    let end = dedented.iter().rposition(|l| !l.is_empty()).map(|i| i + 1).unwrap_or(0);
    dedented[start..end].join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_preprocess_simple() {
        let src = r#"event Foo(int);
fun bar(x: int) : int {
    if x > 10:
        return x * 2
    return x
}
table T(a:int) := add { Foo(a) };"#;

        let (processed, bodies) = preprocess_fun_bodies(src);
        assert_eq!(bodies.len(), 1);
        assert!(bodies[0].contains("if x > 10:"));
        assert!(processed.contains("\"__PYBODY_0__\""));
        assert!(!processed.contains("if x > 10:"));
    }
}
