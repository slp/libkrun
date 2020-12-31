LDFLAGS = -L/opt/local/lib -lkrun
CFLAGS = -O2 -g -I/opt/local/include

.PHONY: clean

all: chroot_vm

chroot_vm: chroot_vm.c
	gcc -o $@ $< $(CFLAGS) $(LDFLAGS)

clean:
	rm -f chroot_vm
