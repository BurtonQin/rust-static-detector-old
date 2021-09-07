#!/usr/bin/env bash

if [ -z "$1" ]; then
	echo "No detecting directory is provided"
	exit 1
fi

#export CFG_RELEASE_CHANNEL=nightly
#export CFG_RELEASE=1.51.0
#export RUSTC_INSTALL_BINDIR=/home/boqin/.cargo/bin/rustc
#export CFG_COMPILER_HOST_TRIPLE=x86_64-unknown-linux-gnu
export LD_LIBRARY_PATH=/home/boqin/.rustup/toolchains/nightly-2021-01-13-x86_64-unknown-linux-gnu/lib

cargo build --release
#cargo build
export RUSTC=${PWD}/target/release/rust-static-detector
#export DETECTOR_TYPE=UAF
#export DETECTOR_TYPE=AV
export DETECTOR_TYPE=PANIC
export RUST_BACKTRACE=full
export CARGO_INCREMENTAL=0
#export RUST_LOCK_DETECTOR_TYPE=DoubleLockDetector
#export RUST_LOCK_DETECTOR_TYPE=ConflictLockDetector
#export RUST_LOCK_DETECTOR_TYPE=GraphLockDetector
#export RUST_LOCK_DETECTOR_BLACK_LISTS="cc"
#export RUST_LOCK_DETECTOR_WHITE_LISTS="inter,intra,static_ref"

cargo_dir_file=$(realpath cargo_dir.txt)
rm $cargo_dir_file
touch $cargo_dir_file

pushd "$1" > /dev/null
cargo clean
cargo_tomls=$(find . -name "Cargo.toml")
for cargo_toml in ${cargo_tomls[@]}
do
	echo $cargo_toml
	echo $(dirname $cargo_toml) >> $cargo_dir_file
done

IFS=$'\n' read -d '' -r -a lines < ${cargo_dir_file}
for cargo_dir in ${lines[@]}
do
	echo ${cargo_dir}
	pushd ${cargo_dir} > /dev/null
	#cargo check
	cargo build
	#cargo test
	popd > /dev/null
done
popd > /dev/null

#pushd "$1" > /dev/null
#cargo clean
#cargo build
#cargo test
#popd > /dev/null
