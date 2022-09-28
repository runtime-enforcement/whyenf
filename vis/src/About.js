import React, { useEffect, useState } from "react";
import ReactMarkdown from 'react-markdown';
import rehypeRaw from 'rehype-raw'
import Box from '@mui/material/Box';
import Container from '@mui/material/Container';
import Card from '@mui/material/Card';
import CardContent from '@mui/material/CardContent';

export default function About() {
  const [content, setContent] = useState("");

  useEffect(() => {
    fetch("About.md")
      .then((res) => res.text())
      .then((text) => setContent(text));
  }, []);

  return (
    <Box style={{ height: '85vh', margin: 0, padding: 0 }}>
      <Container maxWidth={false} sx={{ pb: 4 }}>
        <Box sx={{ mt: 11 }}>
          <Card variant="outlined">
            <CardContent sx={{ mt: -2 }}>
              <ReactMarkdown rehypePlugins={[rehypeRaw]} children={content} />
            </CardContent>
          </Card>
        </Box>
      </Container>
    </Box>
  );
}
