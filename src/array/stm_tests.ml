open QCheck
open STM

module AConf =
struct

  type cmd =
    | Length
    | Get of int
    | Set of int * char
    | Make of int * char
    | Append
    | Sub of int * int

  let pp_cmd par fmt x =
    let open Util.Pp in
    match x with
    | Length -> cst0 "Length" fmt
    | Get x -> cst1 pp_int "Get" par fmt x
    | Set (x, y) -> cst2 pp_int pp_char "Set" par fmt x y
    | Make (x, y) -> cst2 pp_int pp_char "Make" par fmt x y
    | Append -> cst0 "Append" fmt
    | Sub (x, y) -> cst2 pp_int pp_int "Sub" par fmt x y

  let show_cmd = Util.Pp.to_show pp_cmd

  type state = char list list         (* model *)
  type sut = char Array.t Stack.t

  let arb_cmd s =
    let slen = match s with
      | [] -> 0
      | hd :: _ -> List.length hd in
    let int_gen =
      if slen=0
      then Gen.small_nat
      else Gen.(oneof [small_nat; int_bound (List.length (List.hd s) - 1)]) in
    let len_gen = Gen.small_nat in
    let char_gen = Gen.printable in
    QCheck.make ~print:show_cmd (*~shrink:shrink_cmd*)
      Gen.(oneof (
            [map2 (fun i c -> Make (i,c)) len_gen char_gen;]
            @ (if List.length s < 1 then [] else [
              return Length;
              map (fun i -> Get i) int_gen;
              map2 (fun i c -> Set (i,c)) int_gen char_gen;
              map2 (fun i1 i2 -> Sub (i1, i2)) int_gen int_gen;
            ])
           @
           (if List.length s <= 1
            then []
            else [return Append;])
      ))

  (* let init_state  = [List.init array_size (fun _ -> 'a')] *)
  let init_state = []

  let next_state c s = match c with
    | Length -> s
    | Get _  -> s
    | Set (i,newc) ->
      (match s with
       | [] -> s
       | hd::tl ->
         (List.mapi (fun j curr -> if i=j then newc else curr) hd)::tl)
    | Make (len,newc) ->
      (List.init len (fun _ -> newc))::s
    | Append ->
      (match s with
       | a1::a2::tl -> (a1@a2)::tl
       | [] | _ :: _ -> s
      )
    | Sub (i, l) ->
      (match s with
        | hd :: tl when List.length hd >= (i + l) -> (List.filteri (fun j _ -> (i <= j) && (j < i+l)) hd) :: tl
        | [] | _ :: _ -> s
      )

  let init_sut () : sut = Stack.create ()
  let cleanup sut = Stack.clear sut

  let precond c s = match c with
    | Append -> List.length s >= 2
    | Sub _ | Set _ | Get _ | Length -> List.length s >= 1
    | Make _ -> true

  let get_hd suts = match Stack.top_opt suts with
    | Some t -> t
    | None -> failwith "[Stack.top], stack is empty"

  let push s suts = Stack.push s suts

  let pop suts =
    try
      Stack.pop suts
    with Stack.Empty ->
      failwith "[Stack.pop], stack is empty"

  let run c suts = match c with
    | Length       -> Res (int, Array.length (get_hd suts))
    | Get i        -> Res (result char exn, protect (Array.get (get_hd suts)) i)
    | Set (i,c)    -> Res (result unit exn, protect (fun () -> Array.set (get_hd suts) i c) ())
    | Append -> Res (result unit exn, protect (fun () -> let fst = pop suts in let snd = pop suts in push (Array.append fst snd) suts) ())
    | Sub (i, l)   -> Res (result (array char) exn, protect (fun () ->
        let hd = get_hd suts in
        let sub = Array.sub hd i l in
        let _ = pop suts in
        push sub suts;
        sub) ())
    | Make (len,c) -> Res (result (array char) exn, protect (fun () ->
        let a = Array.make len c in
        push a suts;
        Array.copy a) ())


  let postcond c (s : state) res = match c, res with
    | Length, Res ((Int,_),i) -> i = List.length (List.hd s)
    | Get i, Res ((Result (Char,Exn),_), r) ->
      if i < 0 || i >= List.length (List.hd s)
      then r = Error (Invalid_argument "index out of bounds")
      else r = Ok (List.nth (List.hd s) i)
    | Set (i,_), Res ((Result (Unit,Exn),_), r) ->
      if i < 0 || i >= List.length (List.hd s)
      then r = Error (Invalid_argument "index out of bounds")
      else r = Ok ()
    | Make (len,c), Res ((Result (Array Char,Exn),_), r) ->
      if len < 0
      then r = Error (Invalid_argument "Array.make")
      else r = Ok (Array.init len (fun _ -> c))
    | Append, Res ((Result (Unit,Exn),_), r) ->
      r = Ok ()
    | Sub (i,l), Res ((Result (Array Char,Exn),_), r) ->
      if List.length s = 0 then failwith "should not happen" else
      if i < 0 || l < 0 || i+l > List.length (List.hd s)
      then r = Error (Invalid_argument "Array.sub")
      else r = Ok (Array.of_list (List.filteri (fun j _ -> i <= j && j <= i+l-1) (List.hd s)))
    | _, _ -> false
end

module ArraySTM_seq = STM_sequential.Make(AConf)
;;
QCheck_base_runner.run_tests_main
  (let count = 1000 in
   [ArraySTM_seq.agree_test         ~count ~name:"STM Array test sequential"
])
