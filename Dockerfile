FROM rust:1.86 as builder

RUN apt-get update && apt-get install -y \
    cmake \
    pkg-config \
    libssl-dev \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

WORKDIR /mork

COPY . .

# TODO: follow up with release and remove this when needed
# building the image requires PathMap to be present in the MORK project root folder, until PathMap is released
COPY ./PathMap /PathMap

# needed to compile gxhash
ENV RUSTFLAGS="-C target-cpu=native"

RUN cargo build --release --bin mork_server

FROM debian:bookworm-slim

RUN apt-get update && apt-get install -y \
    libssl3 \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /mork/target/release/mork_server /usr/local/bin/

ENTRYPOINT ["/usr/local/bin/mork_server"]

# mork_server ENV vars:
# MORK_SERVER_ADDR
# MORK_SERVER_PORT

