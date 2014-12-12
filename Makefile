.PHONY: all clean

all:
	ocamlbuild -cflags -w,-8 corinth.d.byte -libs nums

clean:
	ocamlbuild -clean corinth.d.byte
