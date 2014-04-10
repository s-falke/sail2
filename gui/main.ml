(*
  Silly GUI.

  @author Stephan Falke

  Copyright 2009-2014 Stephan Falke

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*)

open GText
open Gtk.Tags
open Gdk.Tags

let tt = ref (Trs.Trs (Signature.createEmpty (), [], Ruletrie.empty ()))
let ff = ref (Formula.Formula [])
let pp = ref ([]: Proof.proof)

let currfolder = ref None

let parsed = ref false
let proved = ref false

let parsedSensitive = ref []
let parsedSensitive2 = ref []

let currname = ref ""
let modified = ref false

let out_some s =
  match s with
    | None -> failwith "Internal error in out_some"
    | Some f -> f

let (_window:[`DELETE_EVENT] GWindow.dialog option ref) = ref None
let window () = out_some !_window

let (_textview:GText.view option ref) = ref None
let textview () = out_some !_textview

let (_genview:GText.view option ref) = ref None
let genview () = out_some !_genview

let (_formulain:GText.view option ref) = ref None
let formulain () = out_some !_formulain

let (_formulaout:GText.view option ref) = ref None
let formulaout () = out_some !_formulaout

let (_button:GButton.button option ref) = ref None
let button () = out_some !_button

let (_notebook:GPack.notebook option ref) = ref None
let notebook () = out_some !_notebook

let (_accel_group:Gtk.accel_group option ref) = ref None
let accel_group () = out_some !_accel_group

let (_position:GMisc.label option ref) = ref None
let position () = out_some !_position

let (_clipboard:GData.clipboard option ref) = ref None
let clipboard () = out_some !_clipboard

let edit_entries = ref []


let rec setParsed p =
  parsed := p;
  setParsedSensitive p !parsedSensitive;
  setParsedSensitive2 p !parsedSensitive2
and setParsedSensitive p l =
  match l with
    | [] -> ()
    | m::mm -> (m#misc#set_sensitive p; setParsedSensitive p mm)
and setParsedSensitive2 p l =
  match l with
    | [] -> ()
    | m::mm -> (m#misc#set_sensitive p; setParsedSensitive2 p mm)


(* Displays a proof in a separate window. *)
let rec proof_dialog (prf:Proof.proof) (f:Formula.formula) =
  let dialog = GWindow.dialog ~title:"Sail" ~border_width:0 ~modal:true () in

  let vbox = dialog#vbox in

  let scroll = GBin.scrolled_window ~hpolicy:`AUTOMATIC
                                    ~vpolicy:`AUTOMATIC ~packing:vbox#add () in

  let textview = GText.view ~width:600 ~height:400 () in


  let button = GButton.button ~stock:`OK () in

  let expbutton = GButton.button ~label:"Export HTML" () in

  dialog#misc#realize ();
  scroll#add (textview#coerce);
  dialog#action_area#add (button#coerce);
  dialog#action_area#add (expbutton#coerce);
  ignore (button#connect#clicked ~callback:(dialog#destroy));
  ignore (expbutton#connect#clicked ~callback:(savef ~proof:true));
  button#misc#grab_focus ();
  textview#set_editable false;
  textview#set_cursor_visible false;
  Formatter.create_tags textview#buffer;
  Formatter.write_proof textview#buffer f prf !tt;
  pp := prf;
  let checkt = Printf.sprintf "\n\nTime spend checking: %.3f msec\n" !Implicit.checkTime
  and prooft = Printf.sprintf "Time spend proving: %.3f msec (Time spend in Yices and CVC3: %.3f msec)\n" !Implicit.proofTime !Implicit.smtTime
  and termit = Printf.sprintf "Time spend in AProVE: %.3f msec\n" !Implicit.terminationTime in
    (
      (textview#buffer)#insert ~tag_names:["size"] checkt;
      (textview#buffer)#insert ~tag_names:["size"] prooft;
      (textview#buffer)#insert ~tag_names:["size"] termit
    );
  dialog#set_default_size ~width:100 ~height:100;
  dialog#show ()

(* tries to prove a formula *)
and proof_dispatcher ttrs terminates f =
  Implicit.apply ttrs terminates f

(* This does all the action! *)
and sailit () =
  let t = textview () in
  let g = genview () in
  let fi = formulain () in
  let fo = formulaout () in
  let b = button () in
  if not !parsed then
    (
      let trsfilename = ref "" in
      try
      (
        let (thefilename, trsfile) = Filename.open_temp_file "TRS" ".trs" in
          trsfilename := thefilename;
          output_string trsfile (t#buffer#get_text ());
          output_string trsfile "\n";
          close_out trsfile;
          let trsinfile = open_in !trsfilename in
            tt := TrsParse.getTrs trsinfile;
            close_in trsinfile;
            Sys.remove !trsfilename;
            let emptysorts = Trs.checkConstructors !tt in
              (
                if emptysorts <> [] then
                  let empt = String.concat "\n" emptysorts in
                    raise (TrsParse.ParseException (-1, -1, "The following sorts cannot be shown to have at least two constructor ground terms:\n" ^ empt))
              );
            let isLeftLinear = Trs.isLeftLinear !tt
            and isConstructorBased = Trs.isConstructorBased !tt
            and isNonnestedDefined = Trs.isNonnestedDefined !tt
            and isOverlapping = Trs.isOverlapping !tt
            and isZfree = Trs.isZfreeLeft !tt
            and hasIntResConstructor = Trs.hasIntResultConstructor !tt
            and terminates = Terminator.terminates 5 !tt in
              (
                if (isLeftLinear && isConstructorBased && isNonnestedDefined && (not isOverlapping) && isZfree && (not hasIntResConstructor) && terminates) then
                  (
                    let (p1, p2) = Trs.checkComplete !tt in
                      if p1 <> [] || p2 <> [] then
                        let miss = ref "" in
                        (
                          if p1 <> [] then
                          (
                            miss := !miss ^ "\nMissing patterns:\n\t";
                            miss := !miss ^ (String.concat "\n\t" (List.map (fun t -> (Term.toString t)) p1));
                            miss := !miss ^ "\n"
                          );
                          if p2 <> [] then
                          (
                            miss := !miss ^ "\nLHSs where disjunction of constraints is not valid:\n\t";
                            miss := !miss ^ (String.concat "\n\t" (List.map (fun t -> (Term.toString t)) p2));
                            miss := !miss ^ "\n"
                          );
                          raise (TrsParse.ParseException (-1, -1, "Sufficient completeness could not be shown:\n" ^ !miss))
                        )
                  )
                else
                  (
                    let mess = (if isLeftLinear then "" else "\n* it is not left-linear") ^
                               (if isConstructorBased then "" else "\n* it is not constructor-based") ^
                               (if isNonnestedDefined then "" else "\n* it contains nested recursive calls") ^
                               (if isOverlapping then "\n* it is overlapping" else "") ^
                               (if isZfree then "" else "\n* it is not Z-free on the left-hand sides") ^
                               (if hasIntResConstructor then "\n* it has constructors with resulting sort Int" else "") ^
                               (if terminates then "" else "\n* termination could not be shown" ) in
                      raise (TrsParse.ParseException (-1, -1, "Cannot use the TRS because" ^ mess))
                  )
              );
            Formatter.write_trs (g#buffer) !tt;
            (notebook ())#goto_page 1;
            fi#set_editable true;
            b#set_label "Prove";
            setParsed true;
            Impeq.compute !tt;
            Compat.compute !tt;
            (*
            if (Trs.isUnconstrained !tt) then
              Notheory.compute !tt
            else
              ();
            *)
            fi#misc#grab_focus ()
      )
      with
        | TrsParse.ParseException (l, p, m) ->
            setParsed false;
            let md = GWindow.message_dialog ~message:m
                                            ~message_type:`ERROR
                                            ~buttons:GWindow.Buttons.ok
                                            ~modal:true () in
              (ignore (md#run ()); md#destroy ());
            if l <> -1 then
              let pp = if p <> -1 then p-1 else 0 in
                t#buffer#place_cursor ~where:(t#buffer#get_iter (`LINECHAR (l-1, pp)));
                ignore (t#scroll_to_iter (t#buffer#get_iter (`LINECHAR (l-1, pp))))
            else
              ();
            (notebook ())#goto_page 0;
            t#misc#grab_focus ()
    )
  else if not !proved then
    (
      let formulafilename = ref "" in
      try
        let (thefilename, formulafile) = Filename.open_temp_file "FORMULA" ".formula" in
          formulafilename := thefilename;
          output_string formulafile (fi#buffer#get_text ());
          output_string formulafile "\n";
          close_out formulafile;
          let formulainfile = open_in !formulafilename in
            ff := FormulaParse.getFormula !tt formulainfile;
            close_in formulainfile;
            Sys.remove !formulafilename;
            if not (Formula.isFullyTyped !ff) then
              raise (FormulaParse.ParseException (-1, "The formula contains untyped variables."))
            else if not (Formula.isZfreeLeft !ff) then
              raise (FormulaParse.ParseException (-1, "The formula is not Z-free on left-hand sides."))
            else
              (
                let (newff, p) = proof_dispatcher !tt (Terminator.terminates 5) !ff in
                  Formatter.write_formula fo#buffer newff !tt;
                  proof_dialog p !ff;
                  b#set_label "Clear";
                  fi#set_editable false;
                  b#misc#grab_focus ();
                  proved := true
              )
      with
        | FormulaParse.ParseException (p, m) ->
            proved := false;
            let md = GWindow.message_dialog ~message:m
                                            ~message_type:`ERROR
                                            ~buttons:GWindow.Buttons.ok
                                            ~modal:true () in
              (ignore (md#run ()); md#destroy ());
            fi#misc#grab_focus ();
            (*fi#select_region ~start:0 ~stop:0;*)
            let pp = if p <> -1 then p-1 else 0 in
              fi#buffer#place_cursor ~where:(fi#buffer#get_iter (`LINECHAR (0, pp)))
    )
  else
    (
      fi#buffer#set_text "";
      fi#set_editable true;
      fi#misc#grab_focus ();
      fo#buffer#set_text "";
      b#set_label "Prove";
      proved := false
    )


(* Sets the input tab label to l. *)
and set_input_label l =
  let nb = notebook () in
  let lw = nb#get_tab_label (nb#get_nth_page 0) in
  let lbl = GMisc.label_cast lw in
  lbl#set_label l


(* Callback to update cursor pos. *)
and pos_updater buffer poss =
  let iter = buffer#get_iter_at_mark `INSERT in
    let line = iter#line+1 and pos = iter#line_offset+1 in
      poss#set_text ("L " ^ (string_of_int line) ^ " : C " ^ (string_of_int pos))


(* Callback if input is changed. *)
and changed () =
  modified := true;
  proved := false;
  if !parsed then
    (
      setParsed false;
      (formulain ())#buffer#set_text "";
      (formulain ())#set_editable false;
      (formulaout ())#buffer#set_text "";
      (button ())#set_label "Parse";
      (genview ())#buffer#set_text ""
    )
  else
    ();
  set_input_label ("*" ^ !currname)


(* File filters. *)
and all_files () =
  let f = GFile.filter ~name:"All" () in
    f#add_pattern "*"; f

and trs_files () =
  let f = GFile.filter ~name:"Trs files (*.trs)" () in
    f#add_pattern "*.trs"; f

and tes_files () =
  let f = GFile.filter ~name:"AProVE files (*.patrs)" () in
    f#add_pattern "*.patrs"; f

and html_files () =
  let f = GFile.filter ~name:"HTML files (*.html)" () in
    f#add_pattern "*.html"; f

(* Callback for File>Save. *)
and savef ?(aprove = false) ?(html = false) ?(saveas = false) ?(proof = false) () =
  if (not aprove) && (not html) && (not proof) && !currname <> "" then
    let trsoutfile = open_out !currname in
      set_input_label !currname;
      modified := false;
      setParsed false;
      proved := false;
      output_string trsoutfile ((textview ())#buffer#get_text ());
      close_out trsoutfile;
      sailit ()
  else
    let title = if aprove then "Export AProVE" else if (html || proof) then "Export HTML" else if saveas then "Save File As" else "Save File" in
    let dialog = GWindow.file_chooser_dialog ~action:`SAVE
                                             ~title:title
                                             ~parent:(window ()) () in
    dialog#add_button_stock `CANCEL `CANCEL;
    dialog#add_select_button_stock `SAVE `SAVE;
    if aprove then
      dialog#add_filter (tes_files ())
    else if (html || proof) then
      dialog#add_filter (html_files ())
    else
      dialog#add_filter (trs_files ());
    dialog#add_filter (all_files ());
    dialog#set_default_response `SAVE;
    if (!currfolder <> None) then ignore (dialog#set_current_folder (out_some !currfolder));
    let ext = if aprove then ".patrs" else if (html || proof) then ".html" else ".trs" in
    begin
      match dialog#run () with
        | `SAVE -> let f = dialog#filename in
                     (
                       match f with
                         | None -> ()
                         | Some na -> let nam = if istrs na ext then na else (na ^ ext) in
                                        if Sys.file_exists nam then
                                          (
                                            let md = GWindow.message_dialog ~message:(nam ^ " already exists!\nOverwrite?")
                                                                            ~message_type:`QUESTION
                                                                            ~buttons:GWindow.Buttons.yes_no
                                                                            ~modal:true () in
                                              (
                                                match md#run () with
                                                  | `YES -> (
                                                              if aprove then
                                                                doexport nam
                                                              else if html then
                                                                dotohtml nam
                                                              else if proof then
                                                                doproof nam
                                                              else
                                                                dosave nam
                                                            )
                                                  | _ -> ()
                                              );
                                              md#destroy ()
                                            )
                                        else
                                          (
                                            if aprove then
                                              doexport nam
                                            else if html then
                                              dotohtml nam
                                            else if proof then
                                              doproof nam
                                            else
                                              dosave nam
                                          );
                                        currfolder := dialog#current_folder
                     )
        | `DELETE_EVENT | `CANCEL -> ()
    end;
    dialog#destroy ()
and istrs str ext =
  try
    let n = String.length ext in
    let suff = String.sub str (String.length str - n) n in
      if suff = ext then
        true
      else
        false
  with
    | Invalid_argument _ -> false
and dosave nam =
  let trsoutfile = open_out nam in
  output_string trsoutfile ((textview ())#buffer#get_text ());
  close_out trsoutfile;
  currname := nam;
  set_input_label nam;
  modified := false;
  setParsed false;
  proved := false;
  sailit ()
and doexport nam =
  let tesoutfile = open_out nam in
  output_string tesoutfile (Trs.toAProVE !tt);
  output_string tesoutfile "\n";
  close_out tesoutfile
and dotohtml nam =
  let htmloutfile = open_out nam in
  output_string htmloutfile (Trs.toHTML !tt);
  output_string htmloutfile "\n";
  close_out htmloutfile
and doproof nam =
  let htmloutfile = open_out nam in
  output_string htmloutfile (Proof.toHTML !pp !ff (Trs.getDefined !tt));
  let checkt = Printf.sprintf "<BR><BR>Time spend checking: %.3f msec<BR>\n" !Implicit.checkTime
  and prooft = Printf.sprintf "Time spend for the proving: %.3f msec (Time spend in Yices and CVC3: %.3f msec)<BR>\n" !Implicit.proofTime !Implicit.smtTime
  and termit = Printf.sprintf "Time spend in AProVE: %.3f msec<BR>" !Implicit.terminationTime in
    (
      output_string htmloutfile checkt;
      output_string htmloutfile prooft;
      output_string htmloutfile termit;
    );
  output_string htmloutfile "\n";
  close_out htmloutfile

(* Callback for File>Save as. *)
and saveasf () =
  let ocn = !currname in
  currname := "";
  savef ~saveas:true ();
  if !currname = "" then
    currname := ocn
  else
    ();
  if !modified then
    set_input_label ("*" ^ !currname)
  else
    set_input_label !currname


(* Check whether saving is needed. *)
and ask_save () =
  if !modified then
    let name = if !currname <> "" then !currname else "Unnamed file" in
    let md = GWindow.message_dialog ~message:(name ^ " not saved!\nSave now?")
                                    ~message_type:`QUESTION
                                    ~buttons:GWindow.Buttons.yes_no
                                    ~modal:true () in
      md#set_default_response `YES;
      match md#run () with
        | `YES -> md#destroy (); savef ()
        | _ -> md#destroy ()
  else
    ()


(* Callback for File>New. *)
and newf () =
  ask_save ();
  let t = textview () in
  let fi = formulain () in
  let fo = formulaout () in
  let b = button () in
  t#buffer#set_text "";
  t#set_editable true;
  t#set_cursor_visible true;
  fi#buffer#set_text "";
  fo#buffer#set_text "";
  fi#set_editable false;
  b#set_label "Parse";
  setParsed false;
  proved := false;
  modified := false;
  currname := "";
  set_input_label "*";
  (notebook ())#goto_page 0;
  pos_updater t#buffer (position ());
  t#misc#grab_focus ()


(* Callback and stuff for File>Open. *)
and input_string ic =
  try
    let s = input_line ic in
      s ^ "\n" ^ (input_string ic)
  with
    End_of_file -> ""

(* actually open a file *)
and doOpen na folder =
  let t = textview () in
  let fi = formulain () in
  let fo = formulaout () in
  let b = button () in
  let trsinfile = open_in na in
    currname := na;
    t#buffer#set_text (input_string trsinfile);
    pos_updater t#buffer (position ());
    modified := false;
    set_input_label na;
    fi#buffer#set_text "";
    fo#buffer#set_text "";
    fi#set_editable false;
    b#set_label "Parse";
    setParsed false;
    proved := false;
    t#set_editable true;
    t#set_cursor_visible true;
    t#misc#grab_focus ();
    close_in trsinfile;
    currfolder := folder;
    sailit ()

and openf () =
  ask_save ();
  let dialog = GWindow.file_chooser_dialog ~action:`OPEN
                                           ~title:"Open File"
                                           ~parent:(window ()) () in
  dialog#add_button_stock `CANCEL `CANCEL;
  dialog#add_select_button_stock `OPEN `OPEN;
  dialog#set_default_response `OPEN;
  dialog#add_filter (trs_files ());
  dialog#add_filter (all_files ());
  if (!currfolder <> None) then ignore (dialog#set_current_folder (out_some !currfolder));
  begin
    match dialog#run () with
      | `OPEN -> let f = dialog#filename in
                   (
                     match f with
                       | None -> dialog#destroy ()
                       | Some na -> (doOpen na dialog#current_folder; dialog#destroy ())
                   )
      | `DELETE_EVENT | `CANCEL -> dialog#destroy ()
  end


(* Callback for File>Export AProVE. *)
and export () =
  if not !parsed then
    let md = GWindow.message_dialog ~message:"Not yet parsed!"
                                    ~message_type:`ERROR
                                    ~buttons:GWindow.Buttons.ok
                                    ~modal:true () in
      (ignore (md#run ()); md#destroy ())
  else
    savef ~aprove:true ()

(* Callback for File>Export HTML. *)
and exportHTML () =
  if not !parsed then
    let md = GWindow.message_dialog ~message:"Not yet parsed!"
                                    ~message_type:`ERROR
                                    ~buttons:GWindow.Buttons.ok
                                    ~modal:true () in
      (ignore (md#run ()); md#destroy ())
  else
    savef ~html:true ()


(* Callback and stuff for File>Terminator. *)
and update_pbar (pbar:GRange.progress_bar) () =
  pbar#pulse (); while (Glib.Main.iteration false) do () done
and terminate () =
  if not !parsed then
    let md = GWindow.message_dialog ~message:"Not yet parsed!"
                                    ~message_type:`ERROR
                                    ~buttons:GWindow.Buttons.ok
                                    ~modal:true () in
      (ignore (md#run ()); md#destroy ())
  else
    let goon = ref false in
    let timeout = ref (-1) in
    let (_dialo:[`DELETE_EVENT | `OK] GWindow.dialog option ref) = ref None in

    _dialo := Some (GWindow.dialog ~title:"Terminator" ~allow_grow:false
                                   ~allow_shrink:false ());
    let dialog = out_some !_dialo in
    let table = GPack.table ~rows:1 ~columns:2 ~homogeneous:false ~packing:dialog#vbox#add () in
    let _ = GMisc.label ~text:"Timeout:" ~packing:(table#attach ~left:0 ~top:0) () in
    let adj = GData.adjustment ~value:5.0 ~lower:1.0 ~upper:120.0 ~step_incr:1.0
                               ~page_incr:5.0 ~page_size:0.0 () in
    let spinner = GEdit.spin_button ~adjustment:adj ~rate:0.0 ~digits:0 ~wrap:true
                                    ~packing:(table#attach ~left:1 ~top:0) () in
    table#set_border_width 10;
    table#set_col_spacings 10;
    dialog#add_button_stock `CANCEL `DELETE_EVENT;
    dialog#add_button_stock `OK `OK;
    dialog#set_default_response `OK;
    let childs = dialog#action_area#children in
    let okb = (List.nth childs 0) in
    okb#misc#grab_focus ();
    if dialog#run () = `OK then
      (goon := true; timeout := spinner#value_as_int)
    else
      ();
    dialog#destroy ();
    if !goon then
      (
        _dialo := Some (GWindow.dialog ~title:"Please wait" ~border_width:10 ~allow_grow:false
                                       ~allow_shrink:false ());
        let dialog = out_some !_dialo in
        let table = GPack.table ~rows:2 ~columns:1 ~homogeneous:false ~packing:dialog#vbox#add () in
        let pbar = GRange.progress_bar ~pulse_step:0.1
                                       ~packing:(table#attach ~left:0 ~top:1) () in
        let _ = GMisc.label ~text:"AProVE is attempting a termination proof..."
                            ~packing:(table#attach ~left:0 ~top:0) () in
        ignore (dialog#event#connect#delete ~callback:(fun _ -> true));
        dialog#show ();
        let res = Terminator.terminator !tt (Some (update_pbar pbar)) !timeout in
          let msg = ref "LALA" and msgt = ref `INFO in
            (
              dialog#destroy ();
              (
                match res with
                  | (None, false) -> (msg := "AProVE not found!"; msgt := `ERROR)
                  | (None, true) -> (msg := "AProVE timed out!"; msgt := `INFO)
                  | (Some Ynm.Yes, _) -> (msg := "AProVE proved termination!"; msgt := `INFO)
                  | (Some Ynm.No, _) -> (msg := "AProVE proved nontermination!"; msgt := `WARNING)
                  | (Some Ynm.Maybe, _) -> (msg := "AProVE doesn't know..."; msgt := `WARNING)
              );
              let md = GWindow.message_dialog ~message:!msg
                                              ~message_type:!msgt
                                              ~buttons:GWindow.Buttons.ok
                                              ~modal:true () in
                (ignore (md#run ()); md#destroy ())
            )
      )
    else
      ()


(* Callback for File>Quit. *)
and quit () =
  ask_save ();
  Terminator.shutdownAProVE ();
  GMain.Main.quit ()


(* Callback for Help>About. *)
and about () =
  About.about ()


(* Loads a gtk icon. *)
let stock_to_widget s z =
  let img = GMisc.image () in
    img#set_stock s;
    img#set_icon_size z;
    img#coerce


(* Creates the menus. *)
let f m ua isedit (label, callback, ch, emodi, parsedsensi, stocko) =
  if label = "" then
    ignore (GMenu.separator_item ~packing:m#append ())
  else
    match stocko with
      | None ->
        (
          let item = GMenu.menu_item ~use_mnemonic:ua ~label ~packing:m#append () in
            if ua then
              item#add_accelerator ~group:(accel_group ()) ~modi:(emodi @ [`CONTROL]) ~flags:[`VISIBLE] (int_of_char ch)
            else
              ();
            if parsedsensi then
              parsedSensitive := item::(!parsedSensitive)
            else
              ();
            ignore (item#connect#activate ~callback)
        )
      | Some s ->
        (
          let item = GMenu.image_menu_item ~use_mnemonic:ua ~label ~packing:m#append ~image:(stock_to_widget s `MENU) () in
            if isedit then
              edit_entries := !edit_entries @ [item]
            else
              ();
            if ua then
              item#add_accelerator ~group:(accel_group ()) ~modi:(emodi @ [`CONTROL]) ~flags:[`VISIBLE] (int_of_char ch)
            else
              ();
            if parsedsensi then
              parsedSensitive2 := item::(!parsedSensitive2)
            else
              ();
            ignore (item#connect#activate ~callback)
        )

let create_file_menu packing () =
  let file_menu = GMenu.menu ~packing:packing () in
    List.iter (f file_menu true false)
      [("_New", newf, 'n', [], false, Some `NEW);
       ("_Open", openf, 'o', [], false, Some `OPEN);
       ("_Save", savef ~aprove:false ~html:false ~saveas:false ~proof:false, 's', [], false, Some `SAVE);
       ("Save as", saveasf, 's', [`SHIFT], false, Some `SAVE_AS);
       ("", (fun () -> ()), ' ', [], false, None);
       ("Export _AProVE", export, 'a', [], true, Some `CONVERT);
       ("Export _HTML", exportHTML, 'h', [], true, Some `CONVERT);
       ("", (fun () -> ()), ' ', [], false, None);
       ("_Terminator", terminate, 't', [], true, None);
       ("", (fun () -> ()), ' ', [], false, None);
       ("_Quit", quit, 'q', [], false, None)];
    file_menu

let create_help_menu packing () =
  let help_menu = GMenu.menu ~packing:packing () in
    List.iter (f help_menu false false) [("About", about, ' ', [], false, Some `ABOUT)];
    help_menu

let create_go_menu packing () =
  let go_menu = GMenu.menu ~packing:packing () in
    List.iter (f go_menu true false) [("_Go!", sailit, 'g', [], false, Some `EXECUTE)];
    go_menu

let create_edit_menu packing () =
  let edit_menu = GMenu.menu ~packing:packing () in
    List.iter (f edit_menu true true)
      [("Cu_t", (fun () -> (textview ())#buffer#cut_clipboard (clipboard ())), 'x', [], false, Some `CUT);
       ("_Copy", (fun () -> (textview ())#buffer#copy_clipboard (clipboard ())), 'c', [], false, Some `COPY);
       ("_Paste", (fun () -> (textview ())#buffer#paste_clipboard (clipboard ())), 'v', [], false, Some `PASTE)];
    edit_menu

let activate_edit_menu_items () =
  let hasclip = (clipboard ())#text <> None
  and (sel1, sel2) = (textview ())#buffer#selection_bounds in
    let hassel = ((textview ())#buffer#get_text ~start:sel1 ~stop:sel2 ()) <> "" in
      List.iter2 (fun w b -> w#misc#set_sensitive b) !edit_entries [hassel; hassel; hasclip]


(* Adds tabs. *)
let add_input_view (nb:GPack.notebook) =
  let label = GMisc.label ~text:"*" () in
  let fr1 = GBin.frame ~shadow_type:`ETCHED_IN () in
    ignore (nb#append_page ~tab_label:label#coerce fr1#coerce);
  let sw1 = GBin.scrolled_window ~vpolicy:`AUTOMATIC
                                 ~hpolicy:`AUTOMATIC
                                 ~packing:fr1#add () in
  sw1#add ((textview ())#coerce)

let add_gen_view (nb:GPack.notebook) =
  let label = GMisc.label ~text:"Generated" () in
  let fr1 = GBin.frame ~shadow_type:`ETCHED_IN () in
    ignore (nb#append_page ~tab_label:label#coerce fr1#coerce);
  let sw1 = GBin.scrolled_window ~vpolicy:`AUTOMATIC
                                 ~hpolicy:`AUTOMATIC
                                 ~packing:fr1#add () in
  sw1#add ((genview ())#coerce)


(* paran highlighter *)
let oparen_code = Glib.Utf8.to_unichar "(" ~pos:(ref 0)
let cparen_code = Glib.Utf8.to_unichar ")" ~pos:(ref 0)
let osquare_code = Glib.Utf8.to_unichar "[" ~pos:(ref 0)
let csquare_code = Glib.Utf8.to_unichar "]" ~pos:(ref 0)

let rec register_paren_highlighter (buffer:GText.buffer) =
  let tag1 = buffer#create_tag ~name:"paren" [`BACKGROUND "lightgreen"]
  and tag2 = buffer#create_tag ~name:"square" [`BACKGROUND "lightblue"] in
    ignore (buffer#connect#after#mark_set ~callback:(fun _ _ -> paran_highlighter_fun buffer tag1 tag2))
and paran_highlighter_fun buffer paren_highlight_tag square_highlight_tag =
  let x = buffer#get_text ~start:(buffer#start_iter) ~stop:(buffer#get_iter `INSERT) () in
  buffer#remove_all_tags ~start:buffer#start_iter ~stop:buffer#end_iter;
  if x = "" then
    ()
  else
    match x.[String.length x - 1] with
      | ')' -> let hit = buffer#get_iter `INSERT in
               let count = ref (-1) in
                 if hit#nocopy#backward_find_char
                      (fun c -> if c = oparen_code && !count = 0 then
                                  true
                                else if c = cparen_code then
                                  (incr count; false)
                                else if c = oparen_code then
                                  (decr count; false)
                                else
                                  false
                      )
                 then
                   buffer#apply_tag paren_highlight_tag ~start:hit ~stop:hit#forward_char
                 else
                   ()
      | '(' -> let hit = (buffer#get_iter `INSERT)#backward_char in
               let count = ref 0 in
                 if hit#nocopy#forward_find_char
                      (fun c -> if c = cparen_code && !count = 0 then
                                  true
                                else if c = cparen_code then
                                  (incr count; false)
                                else if c = oparen_code then
                                  (decr count; false)
                                else
                                  false
                      )
                 then
                   buffer#apply_tag paren_highlight_tag ~start:hit ~stop:hit#forward_char
                 else
                   ()
      | ']' -> let hit = buffer#get_iter `INSERT in
               let count = ref (-1) in
                 if hit#nocopy#backward_find_char
                      (fun c -> if c = osquare_code && !count = 0 then
                                  true
                                else if c = csquare_code then
                                  (incr count; false)
                                else if c = osquare_code then
                                  (decr count; false)
                                else
                                  false
                      )
                 then
                   buffer#apply_tag square_highlight_tag ~start:hit ~stop:hit#forward_char
                 else
                   ()
      | '[' -> let hit = (buffer#get_iter `INSERT)#backward_char in
               let count = ref 0 in
                 if hit#nocopy#forward_find_char
                      (fun c -> if c = csquare_code && !count = 0 then
                                  true
                                else if c = csquare_code then
                                  (incr count; false)
                                else if c = osquare_code then
                                  (decr count; false)
                                else
                                  false
                      )
                 then
                   buffer#apply_tag square_highlight_tag ~start:hit ~stop:hit#forward_char
                 else
                   ()
      | _ -> ()


(* new-line ignorer *)
let register_newline_ignorer (buffer:GText.buffer) =
  ignore (buffer#connect#changed ~callback:
    (fun () -> let tt = buffer#get_text () in
                 (if tt <> "" && String.get tt (String.length tt - 1) = '\n' then
                   buffer#set_text (String.sub tt 0 (String.length tt - 1)));
    )
  )


(* Main function. *)
let main () =
  Terminator.startupAProVE ();

  _accel_group := Some (GtkData.AccelGroup.create ());

  _window := Some (GWindow.dialog ~title:"Sail" ~border_width:0 ());
  let wind = window () in

  wind#add_accel_group (accel_group ());

  let vbox = wind#vbox in

  _textview := Some (GText.view ~width:600 ~height:400 ());
  let textv = textview () in

  _genview := Some (GText.view ~width:600 ~height:400 ());
  let genv = genview () in

  _clipboard := Some (GData.clipboard Gdk.Atom.clipboard);

  let frame = GBin.frame ~shadow_type:`IN () in
  _formulain := Some (GText.view ~width:600 ~height:20 ~packing:frame#add ());
  _formulaout := Some (GText.view ~width:600 ~height:20 ());
  let fi = formulain () in
  let fo = formulaout () in

  let lab1 = GMisc.label ~text:"Input:" () in
  let lab2 = GMisc.label ~text:"Output:" () in

  let menu_bar = GMenu.menu_bar ~packing:vbox#add () in
  vbox#set_child_packing ~expand:false menu_bar#coerce;
  let file_item = GMenu.menu_item ~label:"File" ~packing:menu_bar#append () in
  let edit_item = GMenu.menu_item ~label:"Edit" ~packing:menu_bar#append () in
  let go_item = GMenu.menu_item ~label:"Go" ~packing:menu_bar#append () in
  let help_item = GMenu.menu_item ~label:"Help" ~packing:menu_bar#append () in
  let _ = create_file_menu file_item#set_submenu () in
  let _ = create_help_menu help_item#set_submenu () in
  let _ = create_go_menu go_item#set_submenu () in
  let _ = create_edit_menu edit_item#set_submenu () in

  ignore (edit_item#connect#select ~callback:(fun () -> activate_edit_menu_items ()));

  let toolbar = GButton.toolbar ~orientation:`HORIZONTAL
                                ~style:`BOTH
                                ~border_width:5
                                ~packing:vbox#add () in
  vbox#set_child_packing ~expand:false toolbar#coerce;
  let _ = toolbar#insert_button ~text:"New"
                                ~tooltip:"Close current file"
                                ~icon:(stock_to_widget `NEW `LARGE_TOOLBAR)
                                ~callback:newf () in
  let _ = toolbar#insert_button ~text:"Open"
                                ~tooltip:"Open a file"
                                ~icon:(stock_to_widget `OPEN `LARGE_TOOLBAR)
                                ~callback:openf () in
  let _ = toolbar#insert_button ~text:"Save"
                                ~tooltip:"Save a file"
                                ~icon:(stock_to_widget `SAVE `LARGE_TOOLBAR)
                                ~callback:savef () in
  let _ = toolbar#insert_button ~text:"Save as"
                                ~tooltip:"Save a file as"
                                ~icon:(stock_to_widget `SAVE_AS `LARGE_TOOLBAR)
                                ~callback:saveasf () in
  let _ = toolbar#insert_button ~text:"Go!"
                                ~tooltip:"Go!"
                                ~icon:(stock_to_widget `EXECUTE `LARGE_TOOLBAR)
                                ~callback:sailit () in

  _button := Some (GButton.button ~label:"Parse" ());
  let b = button () in

  _notebook := Some (GPack.notebook ());
  let nb = notebook () in

  let table = GPack.table ~rows:5
                          ~columns:1
                          ~homogeneous:false
                          ~packing:vbox#add () in

  _position := Some (GMisc.label ~text:"L 1 : C 1" ());
  let poss = position () in

  add_input_view nb;
  add_gen_view nb;
  ignore (wind#connect#destroy ~callback:quit);
  ignore (wind#event#connect#delete ~callback:(fun _ -> quit (); true));
  ignore (b#connect#clicked ~callback:sailit);
  ignore (textv#buffer#connect#changed ~callback:changed);
  ignore (textv#buffer#connect#after#mark_set ~callback:(fun _ _ -> pos_updater textv#buffer poss));
  ignore (fi#buffer#connect#changed ~callback:(Parancount.count fi lab1));
  register_paren_highlighter textv#buffer;
  register_paren_highlighter fi#buffer;
  register_newline_ignorer fi#buffer;
  textv#misc#modify_font_by_name "sans 12";
  table#attach ~left:0 ~top:0 ~expand:`BOTH (nb#coerce);
  table#attach ~left:0 ~top:1 (lab1#coerce);
  table#attach ~left:0 ~top:2 (frame#coerce);
  table#attach ~left:0 ~top:3 (lab2#coerce);
  table#attach ~left:0 ~top:4 (fo#coerce);
  wind#action_area#add (poss#coerce);
  wind#action_area#add (b#coerce);
  fi#set_editable false;
  fo#set_editable false;
  wind#misc#realize ();
  wind#set_default_size ~width:100 ~height:100;
  wind#show ();
  Formatter.create_tags genv#buffer;
  Formatter.create_tags fo#buffer;
  genv#set_editable false;
  genv#set_cursor_visible false;
  textv#misc#grab_focus ();
  setParsed false;
  (
    try
      let filename = Sys.argv.(1) in
        doOpen filename None
    with
      | Invalid_argument "index out of bounds" | Sys_error _ -> ()
  );
  GMain.Main.main ()
