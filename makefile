cc = clang
cflags = -O3 -march=native -pipe -std=c11

src = u.c
bin = u
obj = $(src:.c=.o)

all: $(bin)

$(bin): $(obj)
	$(cc) $(obj) -lm -o $@ $(cflags)

%.o: %.c
	$(cc) $(cflags) -c $< -o $@

clean:
	rm -f $(obj) $(bin)
