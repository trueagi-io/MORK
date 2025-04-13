FROM rust:1.86-alpine AS builder

WORKDIR /mork

COPY . .

# TODO: follow up with release and remove this when needed
COPY ./PathMap /PathMap

RUN apk add --no-cache \
    build-base \
    musl-dev \
    g++ \
    pkgconfig \
    cmake \
    openssl-dev \ 
    openssl-libs-static

RUN rustup target add x86_64-unknown-linux-musl

# needed to compile gxhash
ENV RUSTFLAGS="-C target-cpu=native"

RUN cargo build --release --bin mork_server --target x86_64-unknown-linux-musl

FROM alpine:3.19

COPY --from=builder /mork/target/x86_64-unknown-linux-musl/release/mork_server /usr/local/bin/

RUN rm -rf /var/cache/apk/* /tmp/* /mork

ENTRYPOINT ["/usr/local/bin/mork_server"]
