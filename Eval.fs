module Eval

    open StateMonad

    (* Code for testing *)

    let hello = [('H', 4); ('E', 1); ('L', 1); ('L', 1); ('O', 1);]
    let state = mkState [("x", 5); ("y", 42)] hello ["_pos_"; "_result_"]
    let emptyState = mkState [] [] []
    
    let add (a:SM<int>) (b:SM<int>) =
        a >>=
        (fun v1 -> b >>= (fun v2 -> ret(v1 + v2)))
        
    let sub (a:SM<int>) (b:SM<int>) =
        a >>=
        (fun v1 -> b >>= (fun v2 -> ret(v1 - v2)))
        
    let mul (a:SM<int>) (b:SM<int>) =
        a >>=
        (fun v1 -> b >>= (fun v2 -> ret(v1 * v2)))
        
    
    let div a b =
        a >>=
        (fun v1 -> b >>= (fun v2 -> match v2 with
                                    | v2 when v2 = 0 -> fail(DivisionByZero)
                                    | _ -> ret(v1 / v2)))
    
    let modu a b =
        a >>=
        (fun v1 -> b >>= (fun v2 -> match v2 with
                                    | v2 when v2 = 0 -> fail(DivisionByZero)
                                    | _ -> ret(v1 % v2)))

    type aExp =
        | N of int
        | V of string
        | WL
        | PV of aExp
        | Add of aExp * aExp
        | Sub of aExp * aExp
        | Mul of aExp * aExp
        | Div of aExp * aExp
        | Mod of aExp * aExp
        | CharToInt of cExp
    and cExp =
        | C  of char  (* Character value *)
        | CV of aExp  (* Character lookup at word index *)
        | ToUpper of cExp
        | ToLower of cExp
        | IntToChar of aExp

    type bExp =             
        | TT                   (* true *)
        | FF                   (* false *)
        | AEq of aExp * aExp   (* numeric equality *)
        | ALt of aExp * aExp   (* numeric less than *)
        | Not of bExp          (* boolean not *)
        | Conj of bExp * bExp  (* boolean conjunction *)
        | IsVowel of cExp      (* check for vowel *)
        | IsLetter of cExp     (* check for letter *)
        | IsDigit of cExp      (* check for digit *)

    let (.+.) a b = Add (a, b)
    let (.-.) a b = Sub (a, b)
    let (.*.) a b = Mul (a, b)
    let (./.) a b = Div (a, b)
    let (.%.) a b = Mod (a, b)

    let (~~) b = Not b
    let (.&&.) b1 b2 = Conj (b1, b2)
    let (.||.) b1 b2 = ~~(~~b1 .&&. ~~b2)       (* boolean disjunction *)
    let (.->.) b1 b2 = (~~b1) .||. b2           (* boolean implication *) 
       
    let (.=.) a b = AEq (a, b)   
    let (.<.) a b = ALt (a, b)   
    let (.<>.) a b = ~~(a .=. b)
    let (.<=.) a b = a .<. b .||. ~~(a .<>. b)
    let (.>=.) a b = ~~(a .<. b)                (* numeric greater than or equal to *)
    let (.>.) a b = ~~(a .=. b) .&&. (a .>=. b) (* numeric greater than *)    

    let rec arithEval : aExp -> SM<int> =
        function
        | N n -> ret n
        | V v -> lookup v
        | WL -> wordLength
        | PV v -> arithEval v >>= pointValue
        | Add (a, b) -> add (arithEval a)  (arithEval b)
        | Sub (a, b) -> sub (arithEval a) (arithEval b)
        | Mul (a, b) -> mul (arithEval a) (arithEval b)
        | Div (a,b) -> div (arithEval a) (arithEval b)
        | Mod (a, b) -> modu (arithEval a) (arithEval b)
        | CharToInt c -> charEval c >>= (fun c -> ret(int(c)))
    and charEval : cExp -> SM<char> =
        function
        | C c -> ret c
        | CV a -> arithEval(a) >>= characterValue
        | ToLower c -> charEval c >>= (System.Char.ToLower >> ret)
        | ToUpper c -> charEval c >>= (System.Char.ToUpper >> ret)
        | IntToChar i -> arithEval i >>= (fun i -> ret(char(i)))

    let isVowel l =
        match System.Char.ToUpper l with
        | 'A' | 'E' | 'I' | 'O' | 'U' -> true
        | _ -> false
    
    let rec boolEval : bExp -> SM<bool> =
        function
        | TT -> ret true
        | FF -> ret false
        | AEq (a, b) -> arithEval a >>= (fun i1 -> arithEval b >>= (fun i2 -> ret (i1 = i2)))
        | ALt (a, b) -> arithEval a >>= (fun i1 -> arithEval b >>= (fun i2 -> ret (i1 < i2)))
        | Not b -> boolEval b >>= (fun b -> ret(not b))
        | Conj (a, b) -> boolEval a >>= (fun b1 -> boolEval b >>= (fun b2 -> ret (b1 && b2)))
        | IsVowel c -> charEval c >>= (isVowel >> ret)
        | IsLetter c -> charEval c >>= (System.Char.IsLetter >> ret)
        | IsDigit c -> charEval c >>= (System.Char.IsDigit >> ret)

    type stm =                    (* statements *)
        | Declare of string       (* variable declaration *)
        | Ass of string * aExp    (* variable assignment *)
        | Skip                    (* nop *)
        | Seq of stm * stm        (* sequential composition *)
        | ITE of bExp * stm * stm (* if-then-else statement *)
        | While of bExp * stm     (* while statement *)

    let rec stmntEval : stm -> SM<unit> =
        function
        | Declare s -> declare s
        | Ass (s, a) -> arithEval a >>= update s
        | Skip -> ret ()
        | Seq (stm1, stm2) -> stmntEval stm1 >>>= stmntEval stm2
        | ITE (b, stm1, stm2) -> boolEval b >>= function 
                                                | true -> push >>>= stmntEval stm1 >>>= pop
                                                | false -> push >>>= stmntEval stm2 >>>= pop
        | While (b, stm) -> boolEval b >>= function
                                           | true -> push >>>= stmntEval (While (b, stm)) >>>= pop
                                           | false -> stmntEval Skip

(* Part 3 (Optional) *)

    type StateBuilder() =
        member this.Bind(f, x)    = f >>= x
        member this.Return(x)     = ret x
        member this.ReturnFrom(x) = x
        member this.Delay(f)      = f ()
        member this.Combine(a, b) = a >>= (fun _ -> b)
        
    let prog = new StateBuilder()

    let arithEval2 a = failwith "Not implemented"
    let charEval2 c = failwith "Not implemented"
    let rec boolEval2 b = failwith "Not implemented"

    let stmntEval2 stm = failwith "Not implemented"

(* Part 4 (Optional) *) 

    type word = (char * int) list
    type squareFun = word -> int -> int -> Result<int, Error>

    let stmntToSquareFun stm : squareFun = fun w pos acc ->
        let vars = [("_pos_", pos); ("_acc_", acc); ("_result_", 0)]
        stmntEval stm >>>= lookup "_result_" |> evalSM (mkState vars w (List.map fst vars))

    type coord = int * int
    type boardFun = coord -> Result<squareFun option, Error> 

    let stmntToBoardFun stm m : boardFun = fun coord ->
        let vars = [("_x_", fst coord); ("_y_", snd coord); ("_result_", 0)]
        match stmntEval stm >>>= lookup "_result_" |> evalSM (mkState vars [] (List.map fst vars)) with
        | Failure err -> Failure err
        | Success id -> match Map.tryFind id m with
                        | Some sf -> Success (Some sf)
                        | None    -> Success None

    type board = {
        center        : coord
        defaultSquare : squareFun
        squares       : boardFun
    }

    let mkBoard c defaultSq boardStmnt ids = failwith "Not implemented"
    