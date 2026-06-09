#!/bin/bash

# Directory containing Dockerfile
dir=$1
name=${dir}
# set to docker, podmand or buildah
container_cli=podman

container_export() {
    # Build the image and export the root filesystem
    echo "using ${container_cli}"
    ${container_cli} build -t ${name} ${dir}
    # Create but do not run the container
    container=$(${container_cli} create ${name})
    # export rootfs from ${container_cli}
    echo "created ${container}"
    rm -f ${name}.tar
    ${container_cli} export ${container} -o ${name}.tar
    ${container_cli} rm ${container}
}

resolv_config() {
    # Generate resolv.conf (if needed)
    # resolv.conf is overwrittern after creating a container.
    if ${use_container}; then
    echo "Write resolv.conf"
    echo "search redmond.corp.microsoft.com
    nameserver 10.50.10.50
    nameserver 10.50.50.50
    nameserver 8.8.8.8
    nameserver 10.0.80.11
    nameserver 10.0.80.12
    "> mnt/etc/resolv.conf
    fi
}

# Function to export root filesystem using Buildah
buildah_export() {
    echo "buildah_export"
    buildah bud -t "${name}" "${dir}"
    buildah export "${name}" > ${name}.tar
}

mount_image(){
    # Create root filesystem image
    mkdir -p ./mnt
    sudo umount mnt >> /dev/null
    rm -f ${name}.img
    dd if=/dev/zero of=${name}.img bs=1M count=256
    mkfs.ext4 -F -L linuxroot ${name}.img > /dev/null
    # Mount the image and extract the root filesystem
    sudo mount ${name}.img ./mnt/
    sudo tar -xf $name.tar -C mnt
}


# To Hyper-V disk type
to_vhdx() {
    # Create cpio archive if using inram fs
    # find mnt | cpio -H newc -o > "${name}.cpio"
    sleep 5; sudo umount mnt
    qemu-img convert -O vhdx ${name}.img ${name}.vhdx
    rm -rf mnt ${name}.tar ${name}.img

}

container_export
mount_image
#resolv_config ${use_container_cli}
to_vhdx
