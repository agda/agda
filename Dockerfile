FROM ubuntu:14.04

# Set locale
RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8
ENV DEBIAN_FRONTEND noninteractive
ENV PATH /root/.local/bin/:/opt/ghc/7.10.3/bin:/opt/cabal/1.22/bin:/opt/happy/1.19.5/bin:/opt/alex/3.1.7/bin:$PATH
ENV AGDA_PATH /agda

# Download GHC and cabal
RUN apt-get update && \
    apt-get install -y software-properties-common && \
    add-apt-repository -y ppa:hvr/ghc && \
    apt-key adv --keyserver keyserver.ubuntu.com --recv-keys 575159689BEFB442 && \
    apt-get update && \
    apt-get install -y --force-yes \
        zlib1g-dev libpq-dev libcurl4-gnutls-dev \
        tmux git make g++ tidy \
        libncurses5-dev alex-3.1.7 cabal-install-1.22 ghc-7.10.3 \
        happy-1.19.5

# Install dependencies of agda
RUN mkdir /agda
COPY . /agda/
WORKDIR /agda
RUN cabal update && \
    cabal install --enable-tests --only-dependencies --force-reinstalls;
