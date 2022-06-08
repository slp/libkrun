#include <limits.h>
#include <errno.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <net/if.h>
#include <sys/ioctl.h>
#include <sys/mount.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>


char DEFAULT_KRUN_INIT[] = "/bin/sh";

void set_rlimits(const char *rlimits)
{
    unsigned long long int lim_id, lim_cur, lim_max;
    struct rlimit rlim;
    char *item = (char *) rlimits;

    while (1) {
        lim_id = lim_cur = lim_max = ULLONG_MAX;

        lim_id = strtoull(item, &item, 10);
        if (lim_id == ULLONG_MAX) {
            printf("Invalid rlimit ID\n");
            break;
        }

        item++;
        lim_cur = strtoull(item, &item, 10);
        item++;
        lim_max = strtoull(item, &item, 10);

        rlim.rlim_cur = lim_cur;
        rlim.rlim_max = lim_max;
        if (setrlimit(lim_id, &rlim) != 0) {
            printf("Error setting rlimit for ID=%lld\n", lim_id);
        }

        if (*item != '\0') {
            item++;
        } else {
            break;
        }
    }
}

#ifdef __ROSETTA__
char rosetta_binary[] = "/macos/rosetta\0";
char binfmt_rosetta[] = ":rosetta:M:0:\\x7fELF\\x02\\x01\\x01\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\x00\\x02\\x00\\x3e\\x00:\\xff\\xff\\xff\\xff\\xff\\xfe\\xfe\\x00\\xff\\xff\\xff\\xff\\xff\\xff\\xff\\xff\\xfe\\xff\\xff\\xff:/macos/rosetta:CF\n";
#endif

int main(int argc, char **argv)
{
    struct ifreq ifr;
#ifdef __ROSETTA__
    int fd;
#endif
    int pid;
    int pipefd[2];
    int sockfd;
    int wstatus;
    char *hostname;
    char *krun_init;
    char *workdir;
    char *rlimits;
    char *passp;

    passp = getenv("KRUN_PASS");
    if (passp) {
        printf("Unlocking LUKS root filesystem\n");

	    if (mount("proc", "/proc", "proc",
		      MS_NODEV | MS_NOEXEC | MS_NOSUID | MS_RELATIME, NULL) < 0) {
		    perror("mount(/proc)");
		    exit(-1);
	    }

	    pipe(pipefd);

	    pid = fork();
	    if (pid == 0) {
            close(pipefd[1]);
		    dup2(pipefd[0], 0);
		    close(pipefd[0]);

		    if (execl("/sbin/cryptsetup", "cryptsetup", "open", "/dev/vda", "luksroot", "-", NULL) < 0) {
                perror("execl");
                exit(-1);
            }
	    } else {
		    write(pipefd[1], passp, strnlen(passp, 128));
		    close(pipefd[1]);
		    waitpid(pid, &wstatus, 0);
	    }

        printf("Mounting LUKS root filesystem\n");

	    if (mount("/dev/mapper/luksroot", "/luksroot", "ext4", 0, NULL) < 0) {
		    perror("mount(/luksroot)");
		    exit(-1);
	    }

	    chdir("/luksroot");

        if (mount(".", "/", NULL, MS_MOVE, NULL)) {
            perror("remount root");
            exit(-1);
        }
        chroot(".");
    }

    if (mount("proc", "/proc", "proc",
              MS_NODEV | MS_NOEXEC | MS_NOSUID | MS_RELATIME, NULL) < 0) {
        perror("mount(/proc)");
        exit(-1);
    }

    if (mount("sysfs", "/sys", "sysfs",
              MS_NODEV | MS_NOEXEC | MS_NOSUID | MS_RELATIME, NULL) < 0) {
        perror("mount(/sys)");
        exit(-1);
    }

    if (mount("cgroup2", "/sys/fs/cgroup", "cgroup2",
              MS_NODEV | MS_NOEXEC | MS_NOSUID | MS_RELATIME, NULL) < 0) {
        perror("mount(/sys/fs/cgroup)");
        exit(-1);
    }

    if (mkdir("/dev/pts", 0755) < 0 && errno != EEXIST) {
        perror("mkdir(/dev/pts)");
        exit(-1);
    }

    if (mount("devpts", "/dev/pts", "devpts",
              MS_NOEXEC | MS_NOSUID | MS_RELATIME, NULL) < 0) {
        perror("mount(/dev/pts)");
        exit(-1);
    }

    if (mkdir("/dev/shm", 0755) < 0 && errno != EEXIST) {
        perror("mkdir(/dev/shm)");
        exit(-1);
    }

    if (mount("tmpfs", "/dev/shm", "tmpfs",
              MS_NOEXEC | MS_NOSUID | MS_RELATIME, NULL) < 0) {
        perror("mount(/dev/shm)");
        exit(-1);
    }

#ifdef __ROSETTA__
    if (access(rosetta_binary, F_OK) == 0) {
        if (mount("binfmt_misc", "/proc/sys/fs/binfmt_misc", "binfmt_misc",
                  MS_NOEXEC | MS_NOSUID | MS_RELATIME, NULL) < 0) {
            perror("mount(binfmt_misc)");
            exit(-1);
        } else {
            fd = open("/proc/sys/fs/binfmt_misc/register", O_WRONLY);
            if (fd >= 0) {
                if (write(fd, &binfmt_rosetta[0], strlen(binfmt_rosetta)) < 0) {
                    perror("write to binfmt_misc");
                }
                close(fd);
            } else {
                perror("open binfmt_misc");
            }
        }
    }
#endif

    /* May fail if already exists and that's fine. */
    symlink("/proc/self/fd", "/dev/fd");

    hostname = getenv("HOSTNAME");
    if (hostname) {
        sethostname(hostname, strlen(hostname));
    }

    setsid();
    ioctl(0, TIOCSCTTY, 1);

    sockfd = socket(AF_INET, SOCK_DGRAM, 0);
    if (sockfd >= 0) {
        memset(&ifr, 0, sizeof ifr);
        strncpy(ifr.ifr_name, "lo", IFNAMSIZ);
        ifr.ifr_flags |= IFF_UP;
        ioctl(sockfd, SIOCSIFFLAGS, &ifr);
        close(sockfd);
    }

    rlimits = getenv("KRUN_RLIMITS");
    if (rlimits) {
        set_rlimits(rlimits);
    }

    workdir = getenv("KRUN_WORKDIR");
    if (workdir) {
        chdir(workdir);
    }

    krun_init = getenv("KRUN_INIT");
    if (!krun_init) {
        krun_init = &DEFAULT_KRUN_INIT[0];
    }
    argv[0] = krun_init;

    execv(argv[0], argv);

    return 0;
}
