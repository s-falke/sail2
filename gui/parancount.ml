(*
  Silly GUI, paran counter.

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

let rec count_parans s =
  count_parans_aux s 0 (String.length s) (0, 0)
and count_parans_aux s i n (o, c) =
  if i < n then
    let cc = String.get s i in
      if cc = '(' then
        count_parans_aux s (i + 1) n (o + 1, c)
      else if cc = ')' then
        count_parans_aux s (i + 1) n (o, c + 1)
      else
        count_parans_aux s (i + 1) n (o, c)
  else
    (o, c)

let count (t:GText.view) (l:GMisc.label) () =
  let text = t#buffer#get_text () in
    let (o, c) = count_parans text in
      if o = c then
        l#set_text "Input:"
      else if o > c then
        (
          let status = Printf.sprintf "missing %d of ')'" (o - c) in
            l#set_text ("Input: " ^ status)
        )
      else
        (
          let status = Printf.sprintf "missing %d of '('" (c - o) in
            l#set_text ("Input: " ^ status)
        )
