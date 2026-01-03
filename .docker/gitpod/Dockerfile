FROM ubuntu:jammy

# Install dependencies
RUN apt-get update && apt-get install -y \
    curl \
    git \
    bash-completion \
    python3 \
    python3-pip \
    sudo \
    && rm -rf /var/lib/apt/lists/*

# Create gitpod user
RUN useradd -l -u 33333 -G sudo -md /home/gitpod -s /bin/bash gitpod \
    && echo 'gitpod ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers

USER gitpod
WORKDIR /home/gitpod

# Install elan (Lean version manager)
RUN curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain none

ENV PATH="/home/gitpod/.elan/bin:${PATH}"

# Workaround for VS Code API version in Gitpod
ENV VSCODE_API_VERSION="1.50.0"

# Pre-accept GitHub SSH fingerprint
RUN mkdir -p ~/.ssh && ssh-keyscan github.com >> ~/.ssh/known_hosts 2>/dev/null || true
