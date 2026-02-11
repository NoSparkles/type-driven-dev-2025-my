FROM ubuntu:25.10

WORKDIR /root

ENV DEBIAN_FRONTEND=noninteractive \
    PATH="/root/.local/bin:/root/.idris2/bin:${PATH}"

RUN apt-get update -y \
  && apt-get install -y \
  build-essential \
  curl \
  git \
  libgmp3-dev \
  libncurses5-dev \
  libncursesw5-dev \
  libx11-dev \
  rlwrap \
  && rm -rf /var/lib/apt/lists/

RUN git clone --filter=blob:none https://github.com/cisco/ChezScheme \
  && cd ChezScheme \
  && git checkout 111e2252775319380f66ee6c14ccc309e670be5c \
  && ./configure --threads \
  && make \
  && make install \
  && cd .. \
  && rm -rf ChezScheme

RUN git clone https://github.com/stefan-hoeck/idris2-pack.git pack \
  && cd pack \
  && git checkout ff798eea65c15c1a87c231e431f1fd97bdbd31e8 \
  && echo scheme | bash -c ./install.bash \
  && cd .. \
  && rm -rf pack

RUN echo 'source <(pack completion-script pack)' >> $HOME/.bashrc

RUN yes yes | pack install-app idris2-lsp

