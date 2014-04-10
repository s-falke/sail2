(*
  Silly GUI, termination analysis.

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

let inc = ref stdin
let outc = ref stdout
let isThere = ref true

let checkForAProVE () =
  try
    Unix.access "./aprove.jar" [Unix.F_OK; Unix.R_OK];
    true
  with
    | Unix.Unix_error _ -> false

let startupAProVE () =
  if not (checkForAProVE ()) then
    isThere := false
  else
    (
      Sys.set_signal Sys.sigpipe (Sys.Signal_handle (fun _ -> isThere := false));
      let (incc, outcc) = Unix.open_process "java -Xmx512m -jar aprove.jar -u bat -t interactive -e patrs" in
        inc := incc;
        outc := outcc
    )

let shutdownAProVE () =
  if !isThere then
    ignore (Unix.close_process (!inc, !outc))

let isDone () =
  match (Unix.select [Unix.descr_of_in_channel !inc] [] [] 0.1) with
    | ([], _, _) -> false
    | _ -> true

let doOutTime c t =
  let ts = string_of_int t in
    output_string c (ts ^ "\n"); flush c

let rec doOut c l =
  match l with
    | [] -> (output_string c ".\n"; flush c);
    | t::tt -> (output_string c (t ^ "\n"); flush c; doOut c tt)

let rec getCrap c =
  let ress = input_line c in
    if ress <> "" then
      getCrap c

let getout x =
  match x with
    | None -> failwith "Internal error in getout"
    | Some y -> y

let terminator (t:Trs.trs) (update_pbar:(unit -> unit) option) timeout =
  if not !isThere then
    (None, false)
  else
    let apro = Trs.toAProVELines t in
      doOutTime !outc timeout;
      doOut !outc apro;
      while not (isDone ()) do
        if update_pbar <> None then
          (getout update_pbar) ()
        else
          ()
      done;
      let res = input_line !inc in
      (
        getCrap !inc;
        if res = "true" then
          (Some Ynm.Yes, false)
        else if res = "false" then
          (Some Ynm.No, false)
        else if res = "timed out" then
          (None, true)
        else
          (Some Ynm.Maybe, false)
      )

let terminates timeout ttrs =
  match (terminator ttrs None timeout) with
    | (None, _) -> false
    | (Some Ynm.Yes, _) -> true
    | (Some Ynm.No, _) -> false
    | (Some Ynm.Maybe, _) -> false
