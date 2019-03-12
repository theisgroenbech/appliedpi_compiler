
OCB=ocamlbuild
BUILD=$(OCB) -pkg ANSITerminal -pkg str

all:
	$(BUILD) main.byte
	$(BUILD) main.native
clean:
	$(OCB) -clean

debug: all
	ocamldebug -I `ocamlfind query ANSITerminal` -I `ocamlfind query str` main.byte
