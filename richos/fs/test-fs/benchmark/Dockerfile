FROM alpine
RUN apk add --update --no-cache openrc procps iproute2 openssh bash 
#openntpd openntpd-openrc
RUN ssh-keygen -A
RUN echo "PermitRootLogin yes" >> /etc/ssh/sshd_config
RUN echo "PermitEmptyPasswords yes" >> /etc/ssh/sshd_config
RUN echo "PasswordAuthentication yes" >> /etc/ssh/sshd_config
RUN passwd -d root

COPY ./files/etc/network/interfaces /etc/network/
COPY ./files/etc/resolv.conf /etc/
# This original script will need tty devices and so remove it.
COPY ./files/etc/inittab /etc/inittab
# Add a init script to show IP address after networking
COPY ./files/etc/init.d/showip /etc/init.d/showip
RUN chmod +x /etc/init.d/showip
RUN sed -i -e "s/ -docker//g" /etc/init.d/* 
RUN sed -i -e "s/ -lxc//g" /etc/init.d/* 
RUN echo "verismo" > /etc/hostname


# Generate Host key
RUN ssh-keygen -A

# Mount special file systems on boot and enable local services:
RUN rc-update add sysfs boot 
RUN rc-update add procfs boot 
RUN rc-update add devfs boot
#RUN rc-update add cgroups boot

# Config networking and run servers.
#RUN rc-update add fsck default
#RUN rc-update add root default
RUN rc-update add localmount default
RUN rc-update add hostname default
# Config datetime
RUN rc-update add openntpd default
RUN rc-update add showip default
RUN rc-update add networking default
RUN rc-update add sshd default

#RUN rc-update add local default
# remove unused files
RUN rm -rf /var/cache/apk/*
RUN rm -rf /usr/share/man/* && rm -rf /usr/share/doc/*
