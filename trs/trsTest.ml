(*
  Silly test program.

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

let tt = ref (Trs.Trs (Signature.createEmpty (), [], Ruletrie.empty ()))

let constraintString c =
  if c = [] then
    "True"
  else
    String.concat " /\\ " (List.map Constraint.toString c)

let boolString b =
  if b then
    "Yes"
  else
    "No"

let main () =
  Printf.printf "Input a trs, followed by C-d:\n";
  flush stdout;
  (
    try
      tt := TrsParse.getTrs stdin;
    with
      | Trs_lexer.Eof -> Printf.printf "\n"; exit 0
      | TrsParse.ParseException (_, _, m) -> Printf.printf "%s\n" m; exit 0
  );
  Printf.printf "\nAProVE:\n%s\n" (Trs.toAProVE !tt);
  Printf.printf "\nSorted:\n%s\n" (Trs.toStringSorts !tt);
  Printf.printf "\nConstructor based: %s\n" (boolString (Trs.isConstructorBased !tt));
  Printf.printf "\nLeft linear: %s\n" (boolString (Trs.isLeftLinear !tt));
  Printf.printf "\nSort dependencies:\n";
  List.iter (fun s -> Printf.printf "\t%s: %s\n" s (String.concat ", " (Trs.getDepSorts !tt s))) (Trs.getSorts !tt);
  Printf.printf "\nSatisfiability of constraints:\n";
  List.iter (fun (Rule.Rule (_, _, c)) -> Printf.printf "\t%s: %s\n" (constraintString c) (Ynm.toString (Decproc.isSatisfiablePAConjunction c))) (Trs.getRules !tt);
  Printf.printf "\nSufficiently complete: ";
  let (res1, res2) = Trs.checkComplete !tt in
    if res1 = [] && res2 = [] then
      Printf.printf "Yes\n"
    else
    (
      Printf.printf "No\n";
      if res1 <> [] then
        Printf.printf "Missing patterns:\n";
        List.iter (fun t -> Printf.printf "\t%s\n" (Term.toString t)) res1;
      if res2 <> [] then
        Printf.printf "Lhs where disjunction of constraints is not valid:\n";
        List.iter (fun t -> Printf.printf "\t%s\n" (Term.toString t)) res2;
    )
