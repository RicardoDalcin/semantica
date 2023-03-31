type var = string

type typeL1 =
    Int
  | Bool
  | TyFun of typeL1 * typeL1
  | TyList of typeL1
  | TyPair of typeL1 * typeL1
  | TyMaybe of typeL1
  | TyId of string
             
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
    ExBool of bool (* foi *)
  | ExNumber of int (* foi *)
  | ExIf of expr * expr * expr (* foi *)
  | ExVar of var (* foi *)
  | ExOperation of operator * expr * expr
  | ExApplication of expr * expr (* foi *)
  | ExFunction of var * typeL1 * expr (* foi *)
  | ExLet of var * typeL1 * expr * expr
  | ExLetRec of var * typeL1 * typeL1 * var * typeL1 * expr * expr
  | ExPair of expr * expr
  | ExFst of expr
  | ExSnd of expr
  | ExNil of typeL1 (* foi *)
  | ExList of expr * expr (* foi *)
  | ExHd of expr (* foi *)
  | ExTl of expr (* foi *)
  | ExMatchL of expr * expr * var * var * expr
  | ExJust of expr
  | ExNothing of typeL1
  | ExMatchM of expr * expr * var * expr

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
         Some (Hashtbl.find gamma x)
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
      Hashtbl.add gamma x fTy;
      let ty1 = typeCheck e1 gamma in
      let t = (match ty1 with
          | Some t' -> Some (TyFun (fTy,t'))
          | _ -> None
        ) in
      Hashtbl.remove gamma x;
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
  | _                             -> None
  
exception NoRuleApplies of string
exception NotImplemented of string

let rec eval (e: expr) gamma = 
  match e with
  | ExNumber (n) -> e
  | ExBool (b) -> e
  | ExIf (e1,e2,e3) ->
      let v1 = eval e1 gamma in
      (match v1 with
       | ExBool (true) -> eval e2 gamma
       | ExBool (false) -> eval e3 gamma
       | _ -> raise (NoRuleApplies "eval: if"))
  | ExVar (x) ->
      (try
         Hashtbl.find gamma x
       with Not_found ->
         raise (NoRuleApplies "eval: var"))
  
  | ExOperation (op, e1, e2) ->
      let v1 = eval e1 gamma in
      let v2 = eval e2 gamma in
      (match (v1,v2) with
       | (ExNumber (n1), ExNumber (n2)) ->
           (match op with
            | OpPlus -> ExNumber (n1 + n2)
            | OpMinus -> ExNumber (n1 - n2)
            | OpTimes -> ExNumber (n1 * n2)
            | OpDiv -> ExNumber (n1 / n2)
            | OpGreater -> ExBool (n1 > n2)
            | OpGorE -> ExBool (n1 >= n2)
            | OpEqual -> ExBool (n1 = n2)
            | OpLorE -> ExBool (n1 <= n2)
            | OpLess -> ExBool (n1 < n2)
            | OpAnd -> ExBool (n1 && n2)
            | OpOr -> ExBool (n1 || n2))
       | _ -> raise (NoRuleApplies "eval: operation"))
  | ExApplication -> raise (NotImplemented "eval: application")
  | ExFunction -> raise (NotImplemented "eval: function")
  | ExLet -> raise (NotImplemented "eval: let")
  | ExLetRec -> raise (NotImplemented "eval: let rec")
  | ExPair -> raise (NotImplemented "eval: pair")
  | ExFst -> raise (NotImplemented "eval: fst")
  | ExSnd -> raise (NotImplemented "eval: snd")
  | ExNil -> raise (NotImplemented "eval: nil")
  | ExList -> raise (NotImplemented "eval: list")
  | ExHd -> raise (NotImplemented "eval: hd")
  | ExTl -> raise (NotImplemented "eval: tl")
  | ExMatchL -> raise (NotImplemented "eval: matchL")
  | ExJust -> raise (NotImplemented "eval: just")
  | ExNothing -> raise (NotImplemented "eval: nothing")
  | ExMatchM -> raise (NotImplemented "eval: matchM")
  | _ -> raise (NoRuleApplies "eval: default")

let hashTable = (Hashtbl.create 1)
let test1 = ExNil Bool
let test2 = ExNumber 5
let test3 = ExBool true
let test4 = ExIf ((ExBool true), (ExNumber 5), (ExNumber 10)) 
let test5 = (ExFunction ("x", Int, (ExBool true)))
let test6 = ExApplication (test5, test2)
let test7 = ExList ((ExNumber 5), (ExList ((ExNumber 6), ExNil Int)))
let test8 = ExHd test7
let test9 = ExTl test7
    
let bad1 = ExIf ((ExBool true), (ExNumber 5), (ExBool false))
let bad2 = ExApplication (test5, test3)
let bad3 = ExList ((ExNumber 5), (ExList ((ExBool false), ExNil Int)))

let testEval1 = eval (test1) hashTable