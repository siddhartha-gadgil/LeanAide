# Use the official lightweight Python image.
# https://hub.docker.com/_/python
FROM ubuntu:22.04


# Copy local code to the container image.
ENV APP_HOME /app
WORKDIR $APP_HOME
COPY LeanCodePrompts ./LeanCodePrompts
COPY *.lean ./
COPY data ./data
COPY results ./results

RUN apt-get update && apt-get install -y git curl python3 python3-pip python3-venv
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s --  -y 
ENV PATH="${APP_HOME}/.elan/bin:${PATH}"
RUN elan default leanprover/lean4:nightly
RUN lake build

CMD exec build/bin/bulkelab