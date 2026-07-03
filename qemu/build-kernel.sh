#!/usr/bin/env bash
# qemu/build-kernel.sh — build an x86_64 btrfs kernel for QEMU tracing runs.
#
# Runs the build inside the btrfs-trace docker image (kernel toolchain +
# pahole for BTF), entirely rootless on the host side.
#
# Usage:
#   bash build-kernel.sh <kernel-src-dir> [make-target...]
#
# Example:
#   bash build-kernel.sh ~/qemu-btrfs/btrfs-devel-for-next
set -euo pipefail

KSRC="${1:?Usage: $0 <kernel-src-dir>}"
shift || true
TARGETS=("${@:-bzImage}")
QEMU_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
IMAGE="${IMAGE:-btrfs-trace:latest}"

docker run --rm \
    -u "$(id -u):$(id -g)" -e HOME=/tmp \
    -v "$KSRC":/work/kernel \
    -v "$QEMU_DIR":/work/qemu:ro \
    -w /work/kernel \
    "$IMAGE" bash -c "
set -euxo pipefail
make defconfig
make kvm_guest.config
scripts/kconfig/merge_config.sh -m .config /work/qemu/kernel.config
make olddefconfig
make -j\$(nproc) ${TARGETS[*]}
"
echo "Kernel image: $KSRC/arch/x86/boot/bzImage"
