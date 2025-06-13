FROM rust:1.86-alpine AS builder

WORKDIR /mork

COPY . .

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

RUN cargo install --branch master --rev db1872d71a286f757fc415a12edb2bbd8932e0b8  --git https://github.com/Adam-Vandervorst/PathMap.git pathmap

RUN cargo build --release --bin mork --target x86_64-unknown-linux-musl

FROM alpine:3.19

COPY --from=builder /mork/target/x86_64-unknown-linux-musl/release/mork /usr/local/bin/

RUN rm -rf /var/cache/apk/* /tmp/* /mork

ENTRYPOINT ["/usr/local/bin/mork"]
