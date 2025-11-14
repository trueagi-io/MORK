# Dockerfile for MORK Environment
# Multi-architecture support: linux/amd64, linux/arm64
# Base: Ubuntu with Rust, CMake, and all required dependencies

# Declare platform arguments (automatically provided by buildx)
ARG TARGETPLATFORM
ARG BUILDPLATFORM

FROM --platform=$TARGETPLATFORM ubuntu:22.04

# Re-declare for use in this stage
ARG TARGETPLATFORM
ARG BUILDPLATFORM
ARG TARGETOS
ARG TARGETARCH

# Prevent interactive prompts during package installation
ENV DEBIAN_FRONTEND=noninteractive

# Install system dependencies
RUN apt-get update && apt-get install -y \
    build-essential \
    cmake \
    git \
    curl \
    ca-certificates \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

# Install Rust (nightly toolchain with pinned version for stability)
ENV RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH=/usr/local/cargo/bin:$PATH \
    RUST_MIN_STACK=16777216 \
    CARGO_NET_GIT_FETCH_WITH_CLI=true

# Use latest nightly for full edition2024 support
ARG RUST_VERSION=nightly

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | \
    sh -s -- -y --default-toolchain ${RUST_VERSION} --profile minimal && \
    chmod -R a+w $RUSTUP_HOME $CARGO_HOME

# Set working directory
WORKDIR /build

# Clone PathMap dependency
ARG PATHMAP_REPO=https://github.com/Adam-Vandervorst/PathMap.git
ARG PATHMAP_BRANCH=master
RUN git clone --depth 1 --branch ${PATHMAP_BRANCH} ${PATHMAP_REPO} PathMap

# Copy MORK source code
COPY . /build/MORK

# Build MORK in release mode with increased stack size and optimization for smaller code
WORKDIR /build/MORK
RUN cargo build --release --verbose

# Set the entrypoint to the built binary
CMD ["/build/MORK/target/release/mork", "--help"]

# Metadata
LABEL maintainer="MORK Team"
LABEL description="MeTTa Optimal Reduction Kernel - Multi-architecture support"
LABEL version="0.1.0"
LABEL org.opencontainers.image.source="https://github.com/trueagi-io/mork"