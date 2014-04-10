(*
  Implementation of ImpEq.

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

type impeq = (string * int * int * (string * int * int) list) list

(* for ImpEq *)
let cache = ref []

(* for ImpEq' *)
let cache' = ref []

let thetrs = ref (Trs.Trs (Signature.createEmpty (), [], Ruletrie.empty ()))
let c = ref []
let doRewrite = ref false

let rec printCache () =
  Printf.printf "\n";
  printCacheAux !cache
and printCacheAux ca =
  match ca with
    | [] -> flush stdout
    | (ru, cs)::ca' -> (printCacheLine ru cs; printCacheAux ca')
and printCacheLine ru cs =
  Printf.printf "Rule: %s\n" (Rule.toString ru);
  printCss cs;
  Printf.printf "\n\n"
and printCss cs =
  match cs with
    | [] -> ()
    | (f, l1, l2, cc)::cs' -> Printf.printf "<%s, %d, %d, {%s}>\n" f l1 l2 (getString cc); printCss cs'
and getString cc =
  match cc with
    | [] -> ""
    | [(f, k1, k2)] -> "<" ^ f ^ ", " ^ (string_of_int k1) ^ ", " ^ (string_of_int k2) ^ ">"
    | (f, k1, k2)::cc' -> "<" ^ f ^ ", " ^ (string_of_int k1) ^ ", " ^ (string_of_int k2) ^ ">, " ^ (getString cc')

(* Computes ImpEq for each rule in a TRS and caches the results. *)
let rec compute ttrs =
  cache := [];
  thetrs := ttrs;
  let rules = Trs.getRules ttrs
  and defs = Trs.getDefined ttrs
  and signa = Trs.getSignature ttrs in
    computeRules rules signa defs
and computeRules rules signa defs =
  match rules with
    | [] -> ()
    | (Rule.Rule (l, r, c'))::rules' -> (
                                          c := c';
                                          doRewrite := false;
                                          let cs = List.flatten (computeRule l (getCalls r defs) signa defs) in
                                            cache := (Rule.Rule (l, r, c'), cs)::!cache;
                                          doRewrite := true;
                                          let cs' = List.flatten (computeRule l (getCalls r defs) signa defs) in
                                            cache' := (Rule.Rule (l, r, c'), cs')::!cache';
                                          computeRules rules' signa defs
                                        )
and getCalls t defs =
  if Term.isVariable t then
    []
  else
    let f = Term.getTopSymbol t in
      if List.mem f defs then
        [t]
      else
        List.concat (List.map (fun t -> getCalls t defs) (Term.getArgs t))
and computeRule l calls signa defs =
  match defs with
    | [] -> []
    | f::fs -> (computeFun l calls signa f)::(computeRule l calls signa fs)
and computeFun l calls signa f =
  let fcalls = List.filter (fun t -> (Term.getTopSymbol t) = f) calls in
    if fcalls = [] then
      fillDummy f signa
    else
      fillReal l fcalls f signa
and fillDummy f signa =
  let n = Signature.getArity signa f in
    fillDummyAll f n
and fillDummyAll f n =
  let res = ref [] in
    for i = 1 to (n - 1) do
      for j = (i + 1) to n do
        res := (f, i, j, [])::!res
      done
    done;
    !res
and fillReal l fcalls f signa =
  let largs = Term.getArgs l
  and g = Term.getTopSymbol l
  and n = Signature.getArity signa f in
    let m = List.length largs
    and res = ref [] in
      for i = 1 to (n - 1) do
        for j = (i + 1) to n do
          let yess = fillRealAux largs m fcalls i j f in
            let newres = List.map (fun l -> List.map (fun (k1, k2) -> (g, k1, k2)) l) yess in
              res := (List.map (fun c -> (f, i, j, c)) newres) @ !res
        done
      done;
      !res
and fillRealAux largs m fcalls i j f =
  let list = constructPairList m in
    getSolsFromList largs list (constructRhs fcalls i j) f
and constructRhs fcalls i j =
  match fcalls with
    | [] -> Formula.True
    | _ -> Formula.Formula (List.map (constructRhsAux i j) fcalls)
and constructRhsAux i j t =
  let args = Term.getArgs t in
    Formula.Atom (List.nth args (i - 1), List.nth args (j - 1), [])
and constructPairList m =
  let resi = ref [] in
    for i = 1 to (m - 1) do
      for j = (i + 1) to m do
        resi := (i, j)::!resi
      done
    done;
    !resi
and getSolsFromList largs plist rhs f =
  getMin (getSolsFromListAux largs plist rhs (getZeros (List.length plist)) f)
and getSolsFromListAux largs plist rhs bin f =
  let lhs = constructLhs largs plist bin in
    let rest = if isLast bin then [] else (getSolsFromListAux largs plist rhs (getNext bin) f) in
      if (Formula.isZfree rhs) && (Formula.isValidLIACImplicationConstraint !thetrs !c lhs rhs) = Ynm.Yes then
        (getSol plist bin)::rest
      else if !doRewrite && (doesRewrite !thetrs !c largs f rhs) then
        (getSol plist bin)::rest
      else
        rest
and constructLhs largs plist bin =
  match bin with
    | [] -> Formula.True
    | _ -> constructLhsAux largs plist bin
and constructLhsAux largs plist bin =
  Formula.Formula (myMap2 largs plist bin)
and myMap2 largs plist bin =
  match bin with
    | [] -> []
    | i::bin' -> let (k1, k2) = List.hd plist in
                   if i = 0 then
                     myMap2 largs (List.tl plist) bin'
                   else
                     (Formula.Atom (List.nth largs (k1 - 1), List.nth largs (k2 - 1), []))::(myMap2 largs (List.tl plist) bin')
and getSol plist bin =
  match bin with
    | [] -> []
    | i::bin' -> if i = 1 then
                   (List.hd plist)::(getSol (List.tl plist) bin')
                 else
                   getSol (List.tl plist) bin'
and isLast bin =
  List.for_all (fun i -> i = 1) bin
and getNext bin =
  match bin with
    | [] -> failwith "Internal error in Impeq.getNext"
    | i::bin' -> if i = 0 then
                   1::bin'
                 else
                   0::(getNext bin')
and getMin list =
  getMinAux list []
and getMinAux list acc =
  match list with
    | [] -> acc
    | l::list' -> if hasSmaller l list' || hasSmaller l acc then
                    getMinAux list' acc
                  else
                    getMinAux list' (l::acc)
and hasSmaller l list =
  List.exists (fun l' -> List.for_all (fun e -> List.mem e l) l') list
and getZeros n =
  if n = 0 then
    []
  else
    0::(getZeros (n - 1))
and doesRewrite trs c largs f rhs =
  let l1 = List.hd largs
  and l2 = List.hd (List.tl largs)
  and (r1, r2) = splitRhs rhs
  and constrs = Trs.getConstructors trs in
    if (Term.isVariable l1) && (Term.isVariable l2) && ((Term.getVarSort l1) = "Int") && ((Term.getVarSort l2) = "Int") then
      let ns = buildSimpTree (Trs.getRuleTrie trs) (Term.createFun f [r1; r2], (Constraint.Eq (l1, l2))::c) in
        List.for_all (fun (t, _) -> Term.isBasedOn constrs t) ns
    else
      false
and splitRhs rhs =
  match rhs with
    | Formula.Formula [Formula.Atom (r1, r2, [])] -> (r1, r2)
    | _ -> failwith "Internal error in ImpEq.splitRhs"
and buildSimpTree ruletrie tc =
  buildSimpTreeAux ruletrie [tc] []
and buildSimpTreeAux ruletrie todo acc =
  match todo with
    | [] -> acc
    | tc::tcs -> let tc' = doSimpTreeStep ruletrie tc in
                   if tc' = [tc] then
                     buildSimpTreeAux ruletrie tcs (tc::acc)
                   else
                     buildSimpTreeAux ruletrie (tc' @ tcs) acc
and doSimpTreeStep ruletrie (t, c) =
  if (Term.isVariable t) then
    [(t, c)]
  else
    (
      let args = Term.getArgs t in
        let newArgs = getNewArgs ruletrie args c in
          if newArgs = [(args, c)] then
            doRootStep ruletrie t c
          else
            List.map (fun (args', c') -> (Term.createFun (Term.getTopSymbol t) args', c')) newArgs
    )
and getNewArgs ruletrie args c =
  match args with
    | [] -> []
    | arg::aa -> let newa = doSimpTreeStep ruletrie (arg, c) in
                   if newa = [(arg, c)] then
                     List.map (fun (newaa, c') -> (arg::newaa, c')) (getNewArgs ruletrie aa c)
                   else
                     List.map (fun (newarg, c') -> (newarg::aa, c')) newa
and doRootStep ruletrie t c =
  let ru = getRulesFor ruletrie t in
    let res = doAll t ru c in
      if isValid res then
        List.filter (fun (tt, cc) -> Decproc.isSatisfiablePAConjunction cc <> Ynm.No) res
      else
        [(t, c)]
and doAll t ru c =
  match ru with
    | [] -> []
    | (Rule.Rule (l, r, c'))::rus ->
        (
          let sigma = Unification.matchTermsNoException l t in
            match sigma with
              | None -> doAll t rus c
              | Some sigma' -> (Substitution.applyToTerm sigma' r, (List.map (Constraint.applySubstitution sigma') c') @ c)::(doAll t rus c)
        )
and isValid res =
  List.for_all isValidConstraint res
and isValidConstraint (_, c) =
  List.for_all Constraint.isZbased c
and getRulesFor ruletrie t =
  Ruletrie.getRules ruletrie t

(* returns impeq for a list of rules *)
let rec getForRules rules =
  match rules with
    | [] -> ([]: impeq)
    | [ru] -> getForRule ru !cache
    | ru::rules' -> merge (getForRule ru !cache) (getForRules rules')
and getForRules' rules =
  match rules with
    | [] -> ([]: impeq)
    | [ru] -> getForRule ru !cache'
    | ru::rules' -> merge (getForRule ru !cache') (getForRules' rules')
and getForRule ru ca =
  match ca with
    | [] -> failwith "Internal error in Impeq.getForRule"
    | (ru', cs)::ca' -> if ru = ru' then
                          cs
                        else
                          getForRule ru ca'
and merge cs cs' =
  getMinMerge (union cs cs') []
and union cs cs' =
  match cs with
    | [] -> []
    | c::cc -> (unionAll c cs') @ (union cc cs')
and unionAll (f, l1, l2, c) cs' =
  match cs' with
    | [] -> []
    | (g, k1, k2, d)::cs'' -> if f = g && l1 = k1 && l2 = k2 then
                                (f, l1, l2, Util.remdup (c @ d))::unionAll (f, l1, l2, c) cs''
                              else
                                unionAll (f, l1, l2, c) cs''
and getMinMerge cc acc =
  match cc with
    | [] -> acc
    | c::cc' -> if hasSmallerMerge c cc' || hasSmallerMerge c acc then
                  getMinMerge cc' acc
                else
                  getMinMerge cc' (c::acc)
and hasSmallerMerge (f, l1, l2, c) cc =
  List.exists (fun (g, k1, k2, d) -> f = g && l1 = k1 && l2 = k2 && List.for_all (fun e -> List.mem e c) d) cc

(* Returns a string representing [iq]. *)
let rec toString iq =
  String.concat "\n" (List.map (fun (f, l1, l2, c) -> "<" ^ f ^ ", "
                                                        ^ (string_of_int l1)
                                                        ^ ", "
                                                        ^ (string_of_int l2)
                                                        ^ ", {"
                                                        ^ ctoString c
                                                        ^ "}>") iq)
and ctoString c =
  String.concat ", " (List.map (fun (g, k1, k2) -> "<" ^ g ^ ", " ^ (string_of_int k1) ^ ", " ^ (string_of_int k2) ^ ">") c)
