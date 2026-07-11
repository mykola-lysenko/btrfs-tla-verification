FROM ubuntu:26.04

# Toolchain for building the kernel + QEMU/KVM + guest tracing userspace.
# This one image serves two purposes:
#   1. build container: compile the x86_64 btrfs-for-next kernel
#   2. run container:  qemu-system-x86_64 (KVM) boots that kernel with the
#      container rootfs shared via 9p (virtme-ng), so bpftrace, btrfs-progs
#      and python3 installed here are what the guest sees.
#
# Ubuntu 26.04 matters: it ships bpftrace 0.25 — the tracing scripts use
# adjacent-string-literal concatenation, which bpftrace <= 0.20 cannot parse.
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
        build-essential flex bison bc kmod cpio xz-utils zstd \
        libelf-dev libssl-dev libncurses-dev dwarves \
        git ca-certificates rsync file curl \
        python3 python3-pip python3-argcomplete python3-requests \
        qemu-system-x86 qemu-utils virtiofsd \
        udev kbd \
        bpftrace btrfs-progs attr acl \
    && rm -rf /var/lib/apt/lists/*

# virtme-ng: boots a kernel under QEMU with the host (container) rootfs via
# 9p/virtiofs. Prefer the distro package; fall back to PyPI, then GitHub.
RUN apt-get update && apt-get install -y --no-install-recommends virtme-ng \
    && rm -rf /var/lib/apt/lists/* \
    || pip3 install --break-system-packages virtme-ng \
    || pip3 install --break-system-packages \
         "git+https://github.com/arighi/virtme-ng.git"

# Java for TLC (TLA+ model checking / trace validation; no JRE on the host)
RUN apt-get update && apt-get install -y --no-install-recommends \
        default-jre-headless \
    && rm -rf /var/lib/apt/lists/*

# xfstests: the filesystem regression suite, built in-image so the guest can
# run it as a workload engine (see qemu/run-vm-xfstests.sh). Its qgroup and
# quota test groups encode historical race reproducers — pre-built
# adversarial workloads for the trace-validated models.
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
        autoconf automake libtool libtool-bin gettext pkg-config make \
        libacl1-dev libattr1-dev libaio-dev libcap-dev uuid-dev zlib1g-dev \
        liburing-dev libgdbm-dev \
        xfsprogs xfslibs-dev e2fsprogs \
        gawk psmisc quota bc uuid-runtime fio dbench duperemove \
    && rm -rf /var/lib/apt/lists/*

# Test users many xfstests cases run as (the numeric-prefix one is optional
# and newer shadow versions gate it behind --badname).
RUN useradd -m fsgqa && useradd -m fsgqa2 \
    && { useradd -m --badname 123456-fsgqa 2>/dev/null \
         || useradd -m --force-badname 123456-fsgqa 2>/dev/null || true; }

RUN git clone --depth 1 https://git.kernel.org/pub/scm/fs/xfs/xfstests-dev.git /opt/xfstests \
    && cd /opt/xfstests \
    && git rev-parse HEAD > GITCOMMIT \
    && make -j"$(nproc)" \
    && rm -rf .git

WORKDIR /work
