#!/usr/bin/env bash

# MORK Docker Build Script
# Supports multi-platform builds for amd64, Apple Silicon (arm64), and Intel Mac
# Usage: ./build.sh [PLATFORM] [OPTIONS]
#
# PLATFORM options:
#   amd64       - Build for AMD64/Intel 64-bit (linux/amd64)
#   arm64       - Build for ARM64/Apple Silicon (linux/arm64)
#   all         - Build for all platforms (default)
#
# OPTIONS:
#   --no-cache  - Build without using cache
#   --push      - Push image to registry (requires login)
#   --load      - Load image into local Docker (single platform only)

set -e

# Configuration
IMAGE_NAME="${MORK_IMAGE_NAME:-mork}"
IMAGE_TAG="${MORK_IMAGE_TAG:-latest}"
DOCKERFILE="./target/docker/Dockerfile"
PATHMAP_BRANCH="${PATHMAP_BRANCH:-master}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Function to print colored messages
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Function to display usage
usage() {
    cat << EOF
MORK Docker Build Script

Usage: $0 [PLATFORM] [OPTIONS]

PLATFORM:
    amd64       Build for AMD64/Intel 64-bit (linux/amd64)
    arm64       Build for ARM64/Apple Silicon (linux/arm64)
    all         Build for all platforms (default)

OPTIONS:
    --no-cache  Build without using cache
    --push      Push image to registry (requires docker login)
    --load      Load image into local Docker (single platform only)
    -h, --help  Display this help message

ENVIRONMENT VARIABLES:
    MORK_IMAGE_NAME    Docker image name (default: mork)
    MORK_IMAGE_TAG     Docker image tag (default: latest)
    PATHMAP_BRANCH     Git branch/tag for PathMap (default: master)

EXAMPLES:
    # Build for all platforms
    $0 all

    # Build for Apple Silicon and load into Docker
    $0 arm64 --load

    # Build for amd64 without cache
    $0 amd64 --no-cache

    # Build and push to registry
    $0 all --push

EOF
    exit 0
}

# Parse arguments
PLATFORM="all"
EXTRA_ARGS=""
USE_LOAD=false
USE_PUSH=false

while [[ $# -gt 0 ]]; do
    case $1 in
        amd64|arm64|all)
            PLATFORM="$1"
            shift
            ;;
        --no-cache)
            EXTRA_ARGS="$EXTRA_ARGS --no-cache"
            shift
            ;;
        --push)
            USE_PUSH=true
            shift
            ;;
        --load)
            USE_LOAD=true
            shift
            ;;
        -h|--help)
            usage
            ;;
        *)
            log_error "Unknown option: $1"
            usage
            ;;
    esac
done

# Validate platform and load combination
if [ "$USE_LOAD" = true ] && [ "$PLATFORM" = "all" ]; then
    log_error "--load can only be used with a single platform (amd64 or arm64)"
    exit 1
fi

if [ "$USE_PUSH" = true ] && [ "$USE_LOAD" = true ]; then
    log_error "--push and --load cannot be used together"
    exit 1
fi

# Set platform string
case $PLATFORM in
    amd64)
        PLATFORMS="linux/amd64"
        PLATFORM_DESC="AMD64/Intel 64-bit"
        ;;
    arm64)
        PLATFORMS="linux/arm64"
        PLATFORM_DESC="ARM64/Apple Silicon"
        ;;
    all)
        PLATFORMS="linux/amd64,linux/arm64"
        PLATFORM_DESC="All platforms (AMD64 and ARM64)"
        ;;
esac

# Add push or load flag
if [ "$USE_PUSH" = true ]; then
    EXTRA_ARGS="$EXTRA_ARGS --push"
    ACTION="build and push"
elif [ "$USE_LOAD" = true ]; then
    EXTRA_ARGS="$EXTRA_ARGS --load"
    ACTION="build and load"
else
    ACTION="build"
fi

# Check if buildx is available
if ! docker buildx version > /dev/null 2>&1; then
    log_error "Docker buildx is not available. Please install or enable Docker buildx."
    exit 1
fi

# Create builder if it doesn't exist
BUILDER_NAME="mork-builder"
if ! docker buildx inspect "$BUILDER_NAME" > /dev/null 2>&1; then
    log_info "Creating buildx builder: $BUILDER_NAME"
    docker buildx create --name "$BUILDER_NAME" --use
else
    log_info "Using existing buildx builder: $BUILDER_NAME"
    docker buildx use "$BUILDER_NAME"
fi

# Display build information
log_info "========================================="
log_info "MORK Docker Build Configuration"
log_info "========================================="
log_info "Image:          $IMAGE_NAME:$IMAGE_TAG"
log_info "Platform(s):    $PLATFORM_DESC"
log_info "Action:         $ACTION"
log_info "Dockerfile:     $DOCKERFILE"
log_info "PathMap Branch: $PATHMAP_BRANCH"
log_info "========================================="

# Build the image
log_info "Starting Docker build..."
log_info "This may take several minutes (building from local source)..."

# Build from MORK root directory (need local files in context)
cd "$(dirname "$0")/../.."

if docker buildx build \
    --platform "$PLATFORMS" \
    --tag "$IMAGE_NAME:$IMAGE_TAG" \
    --file "$DOCKERFILE" \
    --build-arg PATHMAP_BRANCH="$PATHMAP_BRANCH" \
    $EXTRA_ARGS \
    .; then
    log_success "Docker image built successfully!"
    log_success "Image: $IMAGE_NAME:$IMAGE_TAG"
    log_success "Platform(s): $PLATFORMS"

    if [ "$USE_LOAD" = true ]; then
        log_info "Image loaded into local Docker"
        log_info "Run with: docker run --rm $IMAGE_NAME:$IMAGE_TAG"
    elif [ "$USE_PUSH" = true ]; then
        log_info "Image pushed to registry"
    else
        log_warning "Image built but not loaded or pushed"
        log_info "To load into Docker, use: --load (single platform only)"
        log_info "To push to registry, use: --push"
    fi
else
    log_error "Docker build failed!"
    exit 1
fi

log_info "Build completed successfully!"
