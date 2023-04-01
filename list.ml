type var = string

type typeL1 =
    Int
  | Bool
  | TyFun of typeL1 * typeL1
  | TyList of typeL1
  | TyPair of typeL1 * typeL1
  | TyMaybe of typeL1
             
type operator =
    OpPlus
  | OpMinus
  | OpTimes
  | OpDiv
  | OpGreater
  | OpGorE
  | OpEqual 
  | OpLorE
  | OpLess 
  | OpAnd
  | OpOr

type expr =
    ExBool of bool
  | ExNumber of int
  | ExIf of expr * expr * expr
  | ExVar of var
  | ExOperation of operator * expr * expr
  | ExApplication of expr * expr
  | ExFunction of var * typeL1 * expr
  | ExLet of var * typeL1 * expr * expr
  | ExLetRec of var * typeL1 * typeL1 * var * typeL1 * expr * expr
  | ExPair of expr * expr
  | ExFst of expr
  | ExSnd of expr
  | ExNil of typeL1
  | ExList of expr * expr
  | ExHd of expr
  | ExTl of expr
  | ExMatchL of expr * expr * var * var * expr
  | ExJust of expr
  | ExNothing of typeL1
  | ExMatchM of expr * expr * var * expr

type value =
  | VNumber of int
  | VBool of bool
  | VList of value * value
  | VNil of typeL1
  | VPair of value * value
  | VClosure of var * typeL1 * expr * context
  | VRecClosure of var * typeL1 * typeL1 * var * typeL1 * expr * expr * context
  | VJust of value
  | VNothing of typeL1
and
  context = (string * value) list

let rec compareType ty1 ty2 = match (ty1,ty2) with
  | TyList a, TyList b when a = b -> true
  | TyList a, TyList b when a<>b -> compareType a b
  | (a, b) when a=b -> true
  | _ -> false
;;

let rec typeCheck (e:expr) gamma =
  match e with
  | ExNil (ty)                    -> Some (TyList ty)
  | ExNumber  (_)                 -> Some Int
  | ExBool (_)                    -> Some Bool
  | ExIf (e1,e2,e3)               ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      let ty3 = typeCheck e3 gamma in
      (match (ty1,ty2,ty3) with
       | (Some Bool, Some ty4, Some ty5) ->
           if (compareType ty4 ty5) 
           then Some ty5 
           else None
       | (_,_,_) -> None)
  | ExVar (x)                     ->
      (try
         (* find x in gamma of type (string * typeL1) list *)
         Some (List.assoc x gamma)
       with Not_found ->
         None)
  | ExApplication (e1,e2)         ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some (TyFun (ty3,ty4)), Some ty5) -> 
           if (compareType ty3 ty5) 
           then Some ty4
           else None
       | _ -> None)
  | ExFunction (x,fTy,e1)         ->
      let ty1 = typeCheck e1 ((x, fTy)::gamma) in
      let t = (match ty1 with
          | Some t' -> Some (TyFun (fTy,t'))
          | _ -> None
        ) in
      t
  | ExList (e1,e2)                ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some (TyList ty4)) -> 
           if compareType ty3 ty4 
           then Some (TyList ty3) 
           else None
       | (_,_) -> None)
  | ExHd (e1)                     ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some (TyList ty2)) -> Some ty2
       | _ -> None)
  | ExTl (ExList(e1,e2))          ->
      let (ty1) = (typeCheck e2 gamma) in
      (match (ty1) with
       | (Some (TyList ty2)) -> ty1
       | _ -> None)
  | ExTl (e1)                     ->
      let (ty1) = (typeCheck e1 gamma) in
      (match (ty1) with
       | (Some (TyList ty2)) -> ty1
       | _ -> None)
  | ExOperation (OpPlus,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Int
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpMinus,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Int
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpTimes,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Int
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpDiv,e1,e2)     ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Int
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpGreater,e1,e2) ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpGorE,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpEqual,e1,e2)   ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Bool
           else if ty3 = Bool && ty4 = Bool then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpLorE,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpLess,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Int && ty4 = Int then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExOperation (OpAnd,e1,e2)    ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) ->
           if ty3 = Bool && ty4 = Bool then
             Some Bool
           else
             None
       | (None,_) -> None
       | (_,None) -> None)
  | ExLet (x,tyF,e1,e2)   ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 ((x, tyF)::gamma) in
      let t = (match (ty1,ty2) with
          | (Some ty3, Some ty4) -> 
              if compareType ty3 tyF 
              then Some ty4 
              else None
          | _ -> None) in
      t
  | ExLetRec (x, tyInF, tyOutF, y, ty1, e1, e2) 
    when compareType tyInF ty1  ->
      let gamma1 = (x, (TyFun (tyInF,tyOutF)))::gamma in
      let ty2 = typeCheck e2 gamma1 in
      let ty1 = typeCheck e1 ((y, ty1)::gamma1) in
      let t = (match (ty1,ty2) with
          | (Some ty3, Some ty4) when compareType ty3 tyOutF -> Some ty4
          | (Some ty3, Some ty4) -> None
          | _ -> None) in
      t
  | ExPair (e1, e2)               ->
      let ty1 = typeCheck e1 gamma in
      let ty2 = typeCheck e2 gamma in
      (match (ty1,ty2) with
       | (Some ty3, Some ty4) -> Some (TyPair (ty3, ty4))
       | (None,_) -> None
       | (_,None) -> None)
  | ExFst (e1)                    ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some (TyPair (ty2, ty3))) -> Some ty2
       | _ -> None)
  | ExSnd (e1)                    ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some (TyPair (ty2, ty3))) -> Some ty3
       | _ -> None)
  | ExJust (e1)                   ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some ty1) -> Some (TyMaybe ty1) 
       | None -> None)
  | ExNothing (ty)                -> Some (TyMaybe ty)
  | ExMatchL (e1, e2, x, xs, e3)  ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some TyList tyL) -> 
           let ty2 = typeCheck e2 gamma in
           let gamma1 = (x, tyL)::gamma in
           let gamma2 = (xs, TyList tyL)::gamma1 in
           let ty3 = typeCheck e3 gamma2 in
           (match (ty2, ty3) with
            | (Some ty4, Some ty5) ->
                if (compareType ty4 ty5) 
                then Some ty5 
                else None
            | (_,_) -> None)
       | _ -> None
      )
  | ExMatchM (e1, e2, x, e3)  ->
      let ty1 = typeCheck e1 gamma in
      (match (ty1) with
       | (Some TyMaybe tyM) -> 
           let ty2 = typeCheck e2 gamma in
           let ty3 = typeCheck e3 ((x, tyM)::gamma) in
           (match (ty2, ty3) with
            | (Some ty4, Some ty5) ->
                if (compareType ty4 ty5) 
                then Some ty5 
                else None
            | (_,_) -> None)
       | _ -> None
      )
  | _                             -> None
;;

exception NoRuleApplies of string
exception DivisionByZero of string
exception EmptyListNotAllowed of string

let rec eval (e: expr) gamma = 
  match e with
  | ExNumber (n) -> VNumber (n)
  | ExBool (b) -> VBool (b)
  | ExIf (e1,e2,e3) ->
      let v1 = eval e1 gamma in
      (match v1 with
       | VBool (true) -> eval e2 gamma
       | VBool (false) -> eval e3 gamma
       | _ -> raise (NoRuleApplies "Eval error: if"))
  | ExVar (x) ->
      (* search for x in gamma of type (string * value) list *)
      let rec search (x: string) (gamma: (string * value) list) = 
        (match gamma with
          | [] -> raise (NoRuleApplies ("Eval error: var " ^ x))
          | (y,v)::tl -> if x = y then v else search x tl)
      in
      search x gamma
  | ExOperation (op, e1, e2) ->
      let v1 = eval e1 gamma in
      let v2 = eval e2 gamma in
      (match (v1,v2) with
       | (VNumber (n1), VNumber (n2)) ->
           (match op with
            | OpPlus -> VNumber (n1 + n2)
            | OpMinus -> VNumber (n1 - n2)
            | OpTimes -> VNumber (n1 * n2)
            | OpDiv ->
                (match n2 with
                | 0 -> raise (DivisionByZero "Eval error: div - division by zero is not allowed")
                | _ -> VNumber (n1 / n2))
            | OpGreater -> VBool (n1 > n2)
            | OpGorE -> VBool (n1 >= n2)
            | OpEqual -> VBool (n1 = n2)
            | OpLorE -> VBool (n1 <= n2)
            | OpLess -> VBool (n1 < n2)
            | _ -> raise (NoRuleApplies "Eval error: operation"))
       | (VBool (b1), VBool (b2)) ->
           (match op with
            | OpAnd -> VBool (b1 && b2)
            | OpOr -> VBool (b1 || b2)
            | OpEqual -> VBool (b1 = b2)
            | _ -> raise (NoRuleApplies "Eval error: operation"))
       | _ -> raise (NoRuleApplies "Eval error: operation"))
  | ExApplication (e1, e2) ->
      let v1 = eval e1 gamma in
      let v2 = eval e2 gamma in
        (match v1 with
        | VClosure (x, fTy, e1, gamma1) ->
            let gamma2 = (x, v2)::gamma1 in
            let v3 = eval e1 gamma2 in
            v3
        | _ -> raise (NoRuleApplies "Eval error: application"))
  (* function must bind the variables used in the body at declaration time *)
  | ExFunction (x, fTy, e1) ->
      VClosure (x, fTy, e1, gamma)
  | ExLet (x, tyF, e1, e2) ->
      (* if e1 is a function, then it must bind the variables used in the body at declaration time *)
      (match e1 with
       | ExFunction (y, fTy, e1) ->
            let v1 = VClosure (y, fTy, e1, gamma) in
            let v2 = eval e2 ((x, v1)::gamma) in
            v2
       | _ ->
          let v1 = eval e1 gamma in
          let v2 = eval e2 ((x, v1)::gamma) in
          v2)
  | ExLetRec (x, tyInF, tyOutF, y, ty1, e1, e2) ->
     let closure = VRecClosure (x, tyInF, tyOutF, y, ty1, e1, e2, gamma) in
      let v2 = eval e2 ((x, closure)::gamma) in
      v2
  | ExPair (e1, e2) ->
      let v1 = eval e1 gamma in
      let v2 = eval e2 gamma in
      VPair (v1, v2)
  | ExFst (e) ->
      let v = eval e gamma in
      (match v with
       | VPair (v1, v2) -> v1
       | _ -> raise (NoRuleApplies "Eval error: fst"))
  | ExSnd (e) ->
      let v = eval e gamma in
      (match v with
       | VPair (v1, v2) -> v2
       | _ -> raise (NoRuleApplies "Eval error: snd"))
  | ExNil (ty) ->
      VNil (ty)
  | ExList (e1, e2) -> 
      let v1 = eval e1 gamma in
      let v2 = eval e2 gamma in
      VList (v1, v2)
  | ExHd (e) ->
      let v = eval e gamma in
      (match v with
       | VNil (ty) -> raise (EmptyListNotAllowed "Eval error: hd - empty list")
       | VList (v1, v2) -> v1
       | _ -> raise (NoRuleApplies "Eval error: hd"))
  | ExTl (e) -> 
      let v = eval e gamma in
      (match v with
       | VNil (ty) -> raise (EmptyListNotAllowed "Eval error: hd - empty list")
       | VList (v1, v2) -> v2
       | _ -> raise (NoRuleApplies "Eval error: tl"))
  | ExMatchL (e1, e2, x, xs, e3) -> 
      let v1 = eval e1 gamma in
      (match v1 with
       | VNil (ty) -> eval e2 gamma
       | VList (v1, v2) ->
           let v3 = eval e3 ((x, v1)::(xs, v2)::gamma) in
           v3
       | _ -> raise (NoRuleApplies "Eval error: matchL"))
  | ExJust (e) ->
      let v = eval e gamma in
      VJust (v)
  | ExNothing (ty) ->
      VNothing (ty)
  | ExMatchM (e1, e2, x, e3) ->
      let v1 = eval e1 gamma in
      (match v1 with
        | VNothing (ty) -> eval e2 gamma
        | VJust (v1) ->
            let v2 = eval e3 ((x, v1)::gamma) in
            v2
        | _ -> raise (NoRuleApplies "Eval error: matchM"))
;;

let rec typeToString (ty: typeL1) : string =
  match ty with
  | Int  -> "int"
  | Bool -> "bool"
  | TyFun (tp1,tp2) -> "(" ^ (typeToString tp1) ^ " -> " ^ (typeToString tp2) ^ ")"
  | TyList a -> (typeToString a) ^ " list"
  | TyPair (tp1,tp2) -> "(" ^ (typeToString tp1) ^ " * " ^ (typeToString tp2) ^ ")"
  | TyMaybe a -> "maybe " ^ (typeToString a)
;;

let rec exprToString (e: expr) : string =
  match e with
  | ExNumber (x) -> string_of_int x
  | ExBool (b) -> string_of_bool b
  | ExIf (e1,e2,e3) -> "(if " ^ (exprToString e1) ^ " then " ^ (exprToString e2) ^ " else " ^ (exprToString e3) ^ ")"
  | ExVar (x) -> x
  | ExOperation (op, e1, e2) -> 
      (match (op, e1, e2) with
       | (OpPlus, e3, e4) -> "(" ^ (exprToString e3) ^ " + " ^ (exprToString e4) ^ ")"
       | (OpMinus, e3, e4) -> "(" ^ (exprToString e3) ^ " - " ^ (exprToString e4) ^ ")"
       | (OpTimes, e3, e4) -> "(" ^ (exprToString e3) ^ " * " ^ (exprToString e4) ^ ")"
       | (OpDiv, e3, e4) -> "(" ^ (exprToString e3) ^ " div " ^ (exprToString e4) ^ ")"
       | (OpGreater, e3, e4) -> "(" ^ (exprToString e3) ^ " > " ^ (exprToString e4) ^ ")"
       | (OpGorE, e3, e4) -> "(" ^ (exprToString e3) ^ " >= " ^ (exprToString e4) ^ ")"
       | (OpEqual, e3, e4) -> "(" ^ (exprToString e3) ^ " = " ^ (exprToString e4) ^ ")"
       | (OpLorE, e3, e4) -> "(" ^ (exprToString e3) ^ " <= " ^ (exprToString e4) ^ ")"
       | (OpLess, e3, e4) -> "(" ^ (exprToString e3) ^ " < " ^ (exprToString e4) ^ ")"
       | (OpAnd, e3, e4) -> "(" ^ (exprToString e3) ^ " and " ^ (exprToString e4) ^ ")"
       | (OpOr, e3, e4) -> "(" ^ (exprToString e3) ^ " or " ^ (exprToString e4) ^ ")"
      )
  | ExApplication (e1, e2) -> "(" ^ (exprToString e1) ^ " " ^ (exprToString e2) ^ ")"
  | ExFunction (x, tyF, e1) -> "(fn " ^ x ^ ": " ^ (typeToString tyF) ^ " => " ^ (exprToString e1) ^ ")"
  | ExLet (x, tyF, e1, e2) -> "(let " ^ x ^ ": " ^ (typeToString tyF) ^ " = " ^ (exprToString e1) ^ " in " ^ (exprToString e2) ^ ")"
  | ExLetRec (x, tyInF, tyOutF, y, ty1, e1, e2) -> "(let rec " ^ x ^ ": " ^ (typeToString tyInF) ^ "->" ^ (typeToString tyOutF) ^ " = fn " ^ y ^ ": " ^ (typeToString ty1) ^ " => " ^ (exprToString e1) ^ " in " ^ (exprToString e2) ^ ")"
  | ExPair (e1, e2) -> "(" ^ (exprToString e1) ^ ", " ^ (exprToString e2) ^ ")"
  | ExFst (e1) -> "(fst " ^ (exprToString e1) ^ ")"
  | ExSnd (e1) -> "(snd " ^ (exprToString e1) ^ ")"
  | ExNil (ty) -> "(nil: " ^ (typeToString ty) ^ ")"
  | ExList (e1, e2) ->  (exprToString e1) ^ "::" ^ (exprToString e2)
  | ExHd (e1) -> "(hd " ^ (exprToString e1) ^ ")"
  | ExTl (e1) -> "(tl " ^ (exprToString e1) ^ ")"
  | ExMatchL (e1, e2, x, xs, e3) -> "(match " ^ (exprToString e1) ^ " with nil => " ^ (exprToString e2) ^ " | " ^ x ^ "::" ^ xs ^ " => " ^ (exprToString e3) ^ ")" 
  | ExJust (e1) -> "(just " ^ (exprToString e1) ^ ")"
  | ExNothing (ty) -> "(nothing: " ^ (typeToString ty) ^ ")"
  | ExMatchM (e1, e2, x, e3) -> "(match " ^ (exprToString e1) ^ " with nothing => " ^ (exprToString e2) ^ " | just " ^ x ^ " => " ^ (exprToString e3) ^ ")"
;;

let rec testWellTyped (e: expr) =
  let hashTable = [] in
  let ty = typeCheck e hashTable in
  (match (ty) with
   | (Some ty1) -> 
       (print_endline "Expressão bem tipada, com tipo:");
       (print_endline (typeToString ty1));
       true
   | None -> 
       (print_endline "Expressão mal tipada.");
       false
  )
;;

let rec runTest (e: expr) =
  (print_endline "Expressão de entrada:");
  (print_endline (exprToString e));
  let wellTyped = testWellTyped e in
  if(wellTyped)
  then 
    let hashTable = [] in
    let value = eval e hashTable in
    (print_endline "Expressão de saída:");
    (print_endline (exprToString value));
;;
  
let hashTable = []
let test1 = ExNil Bool
let test2 = ExNumber 5
let test3 = ExBool true
let test4 = ExIf ((ExBool true), (ExNumber 5), (ExNumber 10)) 
let test5 = (ExFunction ("x", Int, (ExBool true)))
let test6 = ExApplication (test5, test2)
let test7 = ExList ((ExNumber 5), (ExList ((ExNumber 6), ExNil Int)))
let test8 = ExHd test7
let test9 = ExTl test7
let test10 = ExOperation (OpPlus, test2, test2)
let test11 = ExOperation (OpEqual, test2, test2)
let test12 = ExOperation (OpEqual, test3, test3)
let test13 = ExLet ("x", Int, test2, ExVar("x"))
let test14 = ExLet ("x", Int, test2, ExOperation (OpEqual, ExVar("x"), test2))
let test15 = ExLetRec("sum",
                      Int,Int,
                      "y",
                      Int,
                      ExIf(ExOperation (OpGorE, ExVar "y" , ExNumber 0),
                           ExOperation (OpPlus,(ExVar "y"), ExApplication(ExVar "sum", ExOperation(OpMinus,ExVar "y", ExNumber 1))),
                           ExNumber 0 ),
                      ExApplication(ExVar "sum", ExNumber 5));;
let test16 = ExPair (test2, test7)
let test17 = ExFst test16
let test18 = ExSnd test16
let test19 = ExLetRec (("soma"),
                       (TyList Int), Int, 
                       ("l"), 
                       (TyList Int), 
                       (ExMatchL ((ExVar "l"), 
                                  (ExNumber 0), 
                                  ("x"), 
                                  ("xs"), 
                                  ExOperation (OpPlus, 
                                               (ExVar "x"), 
                                               ExApplication ((ExVar "soma"), (ExVar "xs"))
                                              )
                                 )),
                       (ExApplication ((ExVar "soma"), test7))
                      )
let test20 = ExMatchM ((ExJust (ExNumber 5)), 
                       (ExBool false), 
                       "x", 
                       (ExOperation (OpEqual, 
                                     (ExVar "x"), 
                                     (ExNumber 5)
                                    )
                       )
                      )
    
      
let bad1 = ExIf ((ExBool true), (ExNumber 5), (ExBool false))
let bad2 = ExApplication (test5, test3)
let bad3 = ExList ((ExNumber 5), (ExList ((ExBool false), ExNil Int)))
let bad4 = ExOperation (OpEqual, test2, test3)

let testIf = ExIf ((ExBool true), (ExNumber 5), (ExNumber 10))
let testOperation = ExOperation (OpPlus, (ExNumber 5), (ExNumber 10))
let testPair = ExPair (testIf, (ExNumber 10))
let testFst = ExFst testPair
let testSnd = ExSnd testPair
let testList = ExList ((ExNumber 5), (ExList ((ExNumber 6), ExNil Int)))
let testHd = ExHd testList
let testTl = ExTl testList
let testBoolOperation1 = ExOperation (OpAnd, ExBool true, ExBool false)
let testBoolOperation2 = ExOperation (OpOr, ExBool true, ExBool false)
let testBoolOperation3 = ExOperation (OpEqual, ExBool false, ExBool false)

let testEvalIf = eval testIf []
let testEvalOperation = eval testOperation []
let testEvalPair = eval testPair []
let testEvalFst = eval testFst []
let testEvalSnd = eval testSnd []
let testEvalList = eval testList []
let testEvalHd = eval testHd []
let testEvalTl = eval testTl []
let testEvalBoolOperation1 = eval testBoolOperation1 []
let testEvalBoolOperation2 = eval testBoolOperation2 []
let testEvalBoolOperation3 = eval testBoolOperation3 []

let testEval1 = eval test1 []
let testEval2 = eval test2 []
let testEval3 = eval test3 []
let testEval4 = eval test4 []
let testEval5 = eval test5 []
let testEval6 = eval test6 []
let testEval7 = eval test7 []
let testEval8 = eval test8 []
let testEval9 = eval test9 []
let testEval10 = eval test10 []
let testEval11 = eval test11 []
let testEval12 = eval test12 []
let testEval13 = eval test13 []
let testEval14 = eval test14 []
let testEval15 = eval test15 []
let testEval16 = eval test16 []
let testEval17 = eval test17 []
let testEval18 = eval test18 []
let testEval19 = eval test19 []
let testEval20 = eval test20 []

let testFoo = ExLet ("x", Int, ExNumber 2, 
                      ExLet ("foo", TyFun (Int, Int), ExFunction ("y", Int, ExOperation (OpPlus, ExVar("x"), ExVar("y"))), 
                          ExLet ("x", Int, ExNumber 5, ExApplication (ExVar "foo", ExNumber 10))))
                          
let testFooEval = eval testFoo2 []