default: gui

all: gui cli

gui: force_look
	ocamlbuild -cflags -I,+lablgtk2 -lflags -I,+lablgtk2,lablgtk.cmxa,gtkInit.cmx -libs unix gui.native

gui.d.byte: force_look
	ocamlbuild -cflags -I,+lablgtk2 -lflags -I,+lablgtk2,lablgtk.cma,gtkInit.cmo -libs unix gui.d.byte

cli: force_look
	ocamlbuild -libs unix cli.native

cli.d.byte: force_look
	ocamlbuild -libs unix cli.d.byte

doc: force_look
	ocamlbuild sail2.docdir/index.html

clean: force_look
	ocamlbuild -clean

force_look:
	@true
