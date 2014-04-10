(*
  CVC3 binding.

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

let isSatisfiable f fname =
  let (thefilename, formulafile) = Filename.open_temp_file "FORMULA" ".cvc" in
    output_string formulafile f;
    output_string formulafile ("CHECKSAT " ^ fname ^ ";\n");
    close_out formulafile;
    let icc = Unix.open_process_in ("cvc3 " ^ thefilename) in
      let res = input_line icc in
        (
          ignore (Unix.close_process_in icc);
          Sys.remove thefilename;
          if res = "Satisfiable." then
            Ynm.Yes
          else if res = "Unsatisfiable." then
            Ynm.No
          else
            Ynm.Maybe
        )

let isValid f fname =
  let (thefilename, formulafile) = Filename.open_temp_file "FORMULA" ".cvc" in
    output_string formulafile f;
    output_string formulafile ("QUERY " ^ fname ^ ";\n");
    close_out formulafile;
    let icc = Unix.open_process_in ("cvc3 " ^ thefilename) in
      let res = input_line icc in
        (
          ignore (Unix.close_process_in icc);
          Sys.remove thefilename;
          if res = "Valid." then
            Ynm.Yes
          else if res = "Invalid." then
            Ynm.No
          else
            Ynm.Maybe
        )
