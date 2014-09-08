.PHONY: all clean

all:
	ocamlbuild corinth.d.byte -libs nums

clean:
	ocamlbuild -clean corinth.d.byte
