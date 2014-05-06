default: gui

all: gui cli

gui: make_git_sha1 force_look
	ocamlbuild -cflags -I,+lablgtk2 -lflags -I,+lablgtk2,lablgtk.cmxa,gtkInit.cmx -libs unix gui.native

gui.d.byte: make_git_sha1 force_look
	ocamlbuild -cflags -I,+lablgtk2 -lflags -I,+lablgtk2,lablgtk.cma,gtkInit.cmo -libs unix gui.d.byte

cli: make_git_sha1 force_look
	ocamlbuild -libs unix cli.native

cli.d.byte: make_git_sha1 force_look
	ocamlbuild -libs unix cli.d.byte

doc: force_look
	ocamlbuild sail2.docdir/index.html

clean: force_look
	ocamlbuild -clean
	rm -f git_sha1.ml

make_git_sha1: force_look
	./make_git_sha1.sh git_sha1.ml

force_look:
	@true
