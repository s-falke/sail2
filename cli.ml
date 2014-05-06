(*
  Silly CLI.

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
let ff = ref (Formula.Formula [])
let pp = ref ([]: Proof.proof)

(* Displays a proof. *)
let rec printStatistics f =
  Printf.printf "%s\t" (Checker.toString !Checker.lastVerdict);
  Printf.printf "%s\t" (Formula.toString f);
  Printf.printf "%.3f\t" !Implicit.checkTime;
  Printf.printf "%.3f\t%.3f\t" !Implicit.proofTime (!Implicit.proofTime -. !Implicit.smtTime);
  Printf.printf "%.3f\n" !Implicit.terminationTime;
  flush stdout

(* Tries to prove a formula. *)
and constructProof ttrs terminates f =
  Implicit.apply ttrs terminates f

(* This does all the action! *)
and sailit trsfilename formulafilename =
  let trsinfile = open_in trsfilename in
    tt := TrsParse.getTrs trsinfile;
    close_in trsinfile;
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
      );
      Impeq.compute !tt;
      Compat.compute !tt;
  let formulainfile = open_in formulafilename in
    ff := FormulaParse.getFormula !tt formulainfile;
    close_in formulainfile;
    if not (Formula.isFullyTyped !ff) then
      raise (FormulaParse.ParseException (-1, "The formula contains untyped variables."))
    else if not (Formula.isZfreeLeft !ff) then
      raise (FormulaParse.ParseException (-1, "The formula is not Z-free on left-hand sides."))
    else
    (
      let (f, p) = constructProof !tt (Terminator.terminates 5) !ff in
        pp := p;
        printStatistics f
    )

let dumpHTML trsname formulaname =
  let trshtml = open_out (trsname ^ ".html") in
    output_string trshtml "<HTML><BODY>\n";
    output_string trshtml (Trs.toHTML !tt);
    output_string trshtml "\n</BODY></HTML>\n";
    close_out trshtml;
  let formulahtml = open_out (formulaname ^ ".html")
  and checkt = Printf.sprintf "\n<BR><BR>Time spend checking: %.3f msec" !Implicit.checkTime
  and prooft = Printf.sprintf "\n<BR>Time spend proving: %.3f msec (outside Yices and CVC3: %.3f msec)" !Implicit.proofTime (!Implicit.proofTime -. !Implicit.smtTime)
  and termit = Printf.sprintf "\n<BR>Time spend in AProVE: %.3f msec" !Implicit.terminationTime in
    output_string formulahtml "<HTML><BODY>\n";
    output_string formulahtml (Proof.toHTML !pp !ff (Trs.getDefined !tt));
    output_string formulahtml checkt;
    output_string formulahtml prooft;
    output_string formulahtml termit;
    output_string formulahtml "\n</BODY></HTML>\n";

    close_out trshtml

let trsname = ref ""
let formulaname = ref ""

let rec speclist =
  [
    ("-trs", Arg.Set_string trsname, "    - Set the TRS");
    ("--trs", Arg.Set_string trsname, "");
    ("-formula", Arg.Set_string formulaname, "- Specify the formula");
    ("--formula", Arg.Set_string formulaname, "");
    ("-help", Arg.Unit (fun () -> print_usage (); exit 1), "   - Display this list of options");
    ("--help", Arg.Unit (fun () -> print_usage (); exit 1), "");
    ("-version", Arg.Unit (fun () -> Printf.printf "Sail2\nCopyright 2009-2014 Stephan Falke\nVersion %s\n" Git_sha1.git_sha1; exit 1), "- Display the version of this program");
    ("--version", Arg.Unit (fun () -> Printf.printf "Sail2\nCopyright 2009-2014 Stephan Falke\nVersion %s\n" Git_sha1.git_sha1; exit 1), "")
  ]
and print_usage () =
  Arg.usage speclist usage
and usage = "usage: " ^ Sys.argv.(0) ^ " -trs <filename> -formula <filename>"

let _ =
  Arg.parse speclist (fun f -> print_usage (); exit 1) usage;
  if !trsname = "" || !formulaname = "" then
  (
    print_usage ();
    exit 1
  );
  Terminator.startupAProVE ();
  Printf.printf "%s\t%s\t" !trsname !formulaname;
  sailit !trsname !formulaname;
  Terminator.shutdownAProVE ();
  dumpHTML !trsname !formulaname
