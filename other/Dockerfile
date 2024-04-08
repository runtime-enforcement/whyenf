FROM ubuntu:22.04

RUN apt-get update
RUN apt-get upgrade -y
RUN DEBIAN_FRONTEND=noninteractive apt-get install --no-install-recommends -y opam libgmp-dev m4 python3-pip locales nano git

RUN adduser --disabled-password --gecos "" me
RUN locale-gen en_US.UTF-8 &&\
    echo "export LANG=en_US.UTF-8 LANGUAGE=en_US.en LC_ALL=en_US.UTF-8" >> /home/me/.bashrc

USER me
WORKDIR /home/me

# pip
RUN pip3 install --default-timeout=100 pandas matplotlib tqdm

# opam install
RUN opam init -y --disable-sandboxing
RUN opam update -y
RUN opam switch create 4.13.1
RUN eval `opam env --switch=4.13.1`
RUN opam install -y dune core_kernel base zarith menhir js_of_ocaml js_of_ocaml-ppx \
                    zarith_stubs_js dune-build-info qcheck

ENV WDIR /home/me
WORKDIR ${WDIR}

# Permissions
ADD . ${WDIR}
USER root
RUN chmod 755 /home/me
RUN chown -R me:me *
USER me

# Build EnfPoly/WhyMon/WhyEnf

RUN eval `opam config env`; git clone https://github.com/runtime-enforcement/whyenf.git; cd /home/me/whyenf; git switch artifact; dune build --release
RUN eval `opam config env`; git clone https://bitbucket.org/jshs/monpoly.git; cd /home/me/monpoly; git switch enfpoly; dune build --release
RUN eval `opam config env`; git clone https://github.com/runtime-monitoring/whymon.git; cd /home/me/whymon; git switch whyenf; git checkout e44aee7bb86df2abfef3aa07482f59de22f7a06b; dune build --release

USER root
RUN echo "su - me" >> /root/.bashrc