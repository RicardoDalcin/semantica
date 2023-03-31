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
      Hashtbl.add gamma x tyF;
      let ty2 = typeCheck e2 gamma in
      let t = (match (ty1,ty2) with
          | (Some ty3, Some ty4) -> 
              if compareType ty3 tyF 
              then Some ty4 
              else None
          | _ -> None) in
      Hashtbl.remove gamma x;
      t
  | ExLetRec (x, tyInF, tyOutF, y, ty1, e1, e2) 
    when compareType tyInF ty1  ->
      Hashtbl.add gamma x (TyFun (tyInF,tyOutF));
      let ty2 = typeCheck e2 gamma in
      Hashtbl.add gamma y ty1;
      let ty1 = typeCheck e1 gamma in
      let t = (match (ty1,ty2) with
          | (Some ty3, Some ty4) when compareType ty3 tyOutF -> Some ty4
          | (Some ty3, Some ty4) -> None
          | _ -> None) in
      Hashtbl.remove gamma y;
      Hashtbl.remove gamma x;
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
           Hashtbl.add gamma x tyL;
           Hashtbl.add gamma xs (TyList tyL);
           let ty3 = typeCheck e3 gamma in
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
           Hashtbl.add gamma x tyM;
           let ty3 = typeCheck e3 gamma in
           (match (ty2, ty3) with
            | (Some ty4, Some ty5) ->
                if (compareType ty4 ty5) 
                then Some ty5 
                else None
            | (_,_) -> None)
       | _ -> None
      )
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
            | _ -> raise (NoRuleApplies "eval: operation"))
       | (ExBool (b1), ExBool (b2)) ->
           (match op with
            | OpAnd -> ExBool (b1 && b2)
            | OpOr -> ExBool (b1 || b2)
            | OpEqual -> ExBool (b1 = b2)
            | _ -> raise (NoRuleApplies "eval: operation"))
       | _ -> raise (NoRuleApplies "eval: operation"))
  | ExApplication (e1, e2) -> raise (NotImplemented "eval: application")
  | ExFunction (x, fTy, e1) -> raise (NotImplemented "eval: function")
  | ExLet (x, fTy, e1, e2) -> raise (NotImplemented "eval: let")
  | ExLetRec (var1, ty1, ty2, var2, ty3, e1, e2) -> raise (NotImplemented "eval: letrec")
  | ExPair (e1, e2) ->
      let v1 = eval e1 gamma in
      let v2 = eval e2 gamma in
      ExPair (v1, v2)
  | ExFst (e) ->
      let v = eval e gamma in
      (match v with
       | ExPair (v1, v2) -> v1
       | _ -> raise (NoRuleApplies "eval: fst"))
  | ExSnd (e) ->
      let v = eval e gamma in
      (match v with
       | ExPair (v1, v2) -> v2
       | _ -> raise (NoRuleApplies "eval: snd"))
  | ExNil (ty) ->
      ExNil (ty)
  | ExList (e1, e2) -> 
      let v1 = eval e1 gamma in
      let v2 = eval e2 gamma in
      ExList (v1, v2)
  | ExHd (e) ->
      let v = eval e gamma in
      (match v with
       | ExList (v1, v2) -> v1
       | _ -> raise (NoRuleApplies "eval: hd"))
  | ExTl (e) -> 
      let v = eval e gamma in
      (match v with
       | ExList (v1, v2) -> v2
       | _ -> raise (NoRuleApplies "eval: tl"))
  | ExMatchL (e1, e2, x, xs, e3) -> raise (NotImplemented "eval: matchL")
  | ExJust (e) -> raise (NotImplemented "eval: just")
  | ExNothing (ty) -> raise (NotImplemented "eval: nothing")
  | ExMatchM (e1, e2, x, e3) -> raise (NotImplemented "eval: matchM")

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

let testEvalIf = eval testIf (Hashtbl.create 1)
let testEvalOperation = eval testOperation (Hashtbl.create 1)
let testEvalPair = eval testPair (Hashtbl.create 1)
let testEvalFst = eval testFst (Hashtbl.create 1)
let testEvalSnd = eval testSnd (Hashtbl.create 1)
let testEvalList = eval testList (Hashtbl.create 1)
let testEvalHd = eval testHd (Hashtbl.create 1)
let testEvalTl = eval testTl (Hashtbl.create 1)
let testEvalBoolOperation1 = eval testBoolOperation1 (Hashtbl.create 1)
let testEvalBoolOperation2 = eval testBoolOperation2 (Hashtbl.create 1)
let testEvalBoolOperation3 = eval testBoolOperation3 (Hashtbl.create 1)