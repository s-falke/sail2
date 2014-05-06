(*
  Silly GUI, about dialog.

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

open Gtk.Tags

let icon window =
  let info = GDraw.pixmap_from_xpm_d ~data:Sailxpm.sailxpm ~window () in
    (GMisc.pixmap info ())#coerce

let about () =
  let dialog = GWindow.dialog ~title:"Sail" ~border_width:0 ~modal:true ~no_separator:true () in

  let vbox = dialog#vbox in

  let table = GPack.table ~rows:2
                          ~columns:2
                          ~homogeneous:false
                          ~col_spacings:20
                          ~border_width:20
                          ~packing:vbox#add () in

  let button = GButton.button ~stock:`OK () in

  let label = GMisc.label ~text:("Copyright 2009-2014 Stephan Falke\nVersion " ^ Git_sha1.git_sha1) () in

  dialog#misc#realize ();
  table#attach ~left:0 ~top:0 (icon dialog);
  table#attach ~left:1 ~top:0 (label#coerce);
  table#attach ~left:1 ~top:1 (button#coerce);
  ignore (button#connect#clicked ~callback:(dialog#destroy));
  button#misc#grab_focus ();
  dialog#set_allow_grow false;
  dialog#set_allow_shrink false;
  dialog#set_default_size ~width:100 ~height:100;
  dialog#show ()
