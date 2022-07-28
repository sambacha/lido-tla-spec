# syntax=docker/dockerfile:1.4
FROM ubuntu:focal-20220531

ENV DEBIAN_FRONTEND=noninteractive

USER root

RUN apt-get update && apt-get install -y -qq \
  openjdk-8-jre-headless git locale \
  && rm -rf /var/lib/apt/lists/*

RUN set -eux; \
  	apt-get update; \
    DEBIAN_FRONTEND=noninteractive apt-get install -qqy --assume-yes --no-install-recommends 
    
# Use unicode
RUN locale-gen C.UTF-8 || true
ENV LANG=C.UTF-8
RUN ln -sf /usr/share/zoneinfo/Etc/Zulu /etc/localtime

COPY tools /tools

RUN echo 'alias tla-sany="java -cp /tools/tla2tools.jar tla2sany.SANY"' >> ~/.bashrc
RUN echo 'alias tla-tlc="java -DTLA-Library=/tools/CommunityModules.jar -cp /tools/tla2tools.jar tlc2.TLC"' >> ~/.bashrc
RUN echo 'alias tla-trace="java -cp /tools/tla2tools.jar tlc2.TraceExplorer"' >> ~/.bashrc
RUN echo 'alias tla-repl="java -cp /tools/tla2tools.jar tlc2.REPL"' >> ~/.bashrc

RUN $SHELL
