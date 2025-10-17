# MORK Docker Environment

This directory contains Docker configuration for running MORK (MeTTa Optimal Reduction Kernel) in a containerized environment.

**Key Feature**: This Docker setup uses your **local MORK repository** for building, so any local changes will be included in the image. PathMap is cloned from git during the build.

## Contents

- `Dockerfile` - Multi-stage Dockerfile for building MORK
- `build.sh` - Build script with multi-platform support
- `../.dockerignore` - Files to exclude from Docker build context (at MORK root)

## Quick Start

### Building the Image

Build for all platforms (AMD64 and ARM64):
```bash
./target/docker/build.sh all
```

Build for specific platform:
```bash
# For AMD64/Intel systems
./target/docker/build.sh amd64 --load

# For ARM64/Apple Silicon
./target/docker/build.sh arm64 --load
```

The `--load` flag loads the image into your local Docker daemon (required for single-platform builds if you want to run locally).

### Running MORK in Docker

Once built and loaded, run MORK:
```bash
docker run --rm mork:latest
```

Run with specific command:
```bash
docker run --rm mork:latest mork [your-args]
```

Mount a volume for data persistence:
```bash
docker run --rm -v $(pwd)/data:/mork/data mork:latest
```

## Build Script Options

```bash
./target/docker/build.sh [PLATFORM] [OPTIONS]
```

### Platform Options
- `amd64` - Build for AMD64/Intel 64-bit systems (linux/amd64)
- `arm64` - Build for ARM64/Apple Silicon (linux/arm64)
- `all` - Build for all platforms (default)

### Build Options
- `--no-cache` - Build without using Docker cache
- `--push` - Push image to container registry (requires `docker login`)
- `--load` - Load image into local Docker (single platform only)
- `-h, --help` - Display help message

### Environment Variables
- `MORK_IMAGE_NAME` - Docker image name (default: `mork`)
- `MORK_IMAGE_TAG` - Docker image tag (default: `latest`)
- `PATHMAP_BRANCH` - Git branch/tag for PathMap repository (default: `master`)

## Examples

### Build for local development (Apple Silicon)
```bash
./target/docker/build.sh arm64 --load
```

### Build for local development (Intel Mac or Linux)
```bash
./target/docker/build.sh amd64 --load
```

### Build and push to registry
```bash
export MORK_IMAGE_NAME=myregistry/mork
export MORK_IMAGE_TAG=v0.1.0
docker login myregistry
./target/docker/build.sh all --push
```

### Build without cache (clean build)
```bash
./target/docker/build.sh arm64 --no-cache --load
```

### Build with specific PathMap branch
```bash
export PATHMAP_BRANCH=experimental
./target/docker/build.sh arm64 --load
```

## Architecture

### Multi-Stage Build

The Dockerfile uses a multi-stage build process:

1. **Builder Stage**:
   - Based on `debian:bookworm-slim`
   - Installs Rust nightly toolchain via rustup
   - Installs build dependencies (gcc, cmake, libssl, etc.)
   - **Clones PathMap from git** (https://github.com/Adam-Vandervorst/PathMap.git)
   - **Copies local MORK repository** (including any uncommitted changes)
   - Builds MORK with `--release` flag

2. **Runtime Stage**:
   - Based on minimal `debian:bookworm-slim`
   - Includes only runtime dependencies
   - Runs as non-root user (`mork`)
   - Contains only the compiled binaries

This approach:
- Minimizes the final image size (builder artifacts are discarded)
- Uses your local MORK code (perfect for development and testing)
- Ensures PathMap dependency is always up-to-date from git
- Includes all local changes (even uncommitted ones)

### Multi-Platform Support

The build script uses Docker Buildx to support multiple platforms:
- **linux/amd64** - For Intel/AMD 64-bit systems
- **linux/arm64** - For ARM64 systems (Apple Silicon, ARM servers)

## Requirements

- Docker with buildx support (Docker Desktop includes this)
- Internet connection (to clone PathMap)
- Sufficient disk space for build artifacts (~2GB during build, ~200MB final image)

**Important**: The build uses your local MORK files, so make sure you're in the MORK directory when running the build script.

## Troubleshooting

### Git clone fails for PathMap
If you see errors cloning PathMap:
- Check your internet connection
- Verify https://github.com/Adam-Vandervorst/PathMap.git is accessible
- Try building with a specific branch:
  ```bash
  export PATHMAP_BRANCH=master
  ./target/docker/build.sh arm64 --load
  ```

### Buildx not available
Install or enable Docker Buildx:
```bash
docker buildx version
```

If not available, update Docker Desktop or install the buildx plugin.

### Build fails with memory error
Increase Docker's memory allocation in Docker Desktop settings (Preferences → Resources → Memory).

### Multi-platform build not loading
Multi-platform builds cannot be loaded directly into Docker. Either:
- Build for a single platform with `--load`:
  ```bash
  ./target/docker/build.sh arm64 --load
  ```
- Or push to a registry and pull back:
  ```bash
  ./target/docker/build.sh all --push
  docker pull mork:latest
  ```

### Build context is too large
If the build is slow due to large context:
- Check that `target/` directory is excluded (via `.dockerignore`)
- Remove any large files from the MORK directory
- The `.dockerignore` file should already exclude build artifacts

## Image Details

- **Base Image**: debian:bookworm-slim (both builder and runtime stages)
- **Rust Version**: Nightly (installed via rustup in builder stage)
- **User**: Non-root user `mork` (UID 1000)
- **Working Directory**: `/mork`
- **Data Directory**: `/mork/data` (for mounting volumes)
- **Binaries**: Installed in `/usr/local/bin/`

## Notes

- The Dockerfile installs Rust nightly due to MORK's use of edition 2024 features
- PathMap dependency is cloned from git during build
- **Local MORK files** (including uncommitted changes) are included in the build
- Build artifacts from local builds are excluded via `.dockerignore`
- The image runs as a non-root user for security

## Development Workflow

This Docker setup is ideal for development:

1. **Make changes** to MORK code locally
2. **Build the image** with your changes:
   ```bash
   ./target/docker/build.sh arm64 --load
   ```
3. **Test** the changes in the container:
   ```bash
   docker run --rm mork:latest mork [test-args]
   ```
4. **Iterate** - repeat steps 1-3 as needed

Since the build uses local files, you can test changes before committing them to git.
