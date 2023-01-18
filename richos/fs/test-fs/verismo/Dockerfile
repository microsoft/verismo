FROM alpine as base

RUN apk add --update --no-cache openrc netcat-openbsd procps iproute2 strace openssh bash openntpd

FROM base as verismo-dev
COPY ./files/verismo /verismo
COPY ./files/verismo/user /verismo/user
COPY ./files/verismo/user/* /verismo/user/
RUN apk add build-base automake
RUN cd /verismo/user; make local

FROM base as verismo
RUN ssh-keygen -A
RUN echo "PermitRootLogin yes" >> /etc/ssh/sshd_config
RUN echo "PermitEmptyPasswords yes" >> /etc/ssh/sshd_config
RUN echo "PasswordAuthentication yes" >> /etc/ssh/sshd_config
RUN passwd -d root
RUN rc-update add sysfs default
RUN rc-update add cgroups default
RUN rc-update add procfs default
RUN rc-update add devfs default
RUN rc-update add networking default
RUN rc-update add sshd default
RUN rc-update add openntpd default
COPY ./files/* /
COPY ./files/etc/* /etc/
COPY ./files/etc/network/* /etc/network/
COPY ./files/etc/init.d/* /etc/init.d/
COPY ./files/verismo/verismo.ko /verismo.ko
COPY --from=verismo-dev  /verismo/user/decode_report /verismo/
RUN chmod +x /etc/init.d/verismo && \
    rc-update add verismo default



