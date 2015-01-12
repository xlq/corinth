let rec last = function
    | [] -> raise (Failure "last")
    | [x] -> x
    | x::l -> last l

let rec comma_concat connective strings =
    match strings with
        | [] -> ""
        | [a] -> a
        | [a;b] -> a ^ " " ^ connective ^ " " ^ b
        | a::tail -> a ^ ", " ^ comma_concat connective tail

let unsome = function
    | Some x -> x
    | None -> raise (Failure "unsome")

let rec times n s =
    match n with
        | 0 -> ""
        | n -> s ^ times (n-1) s

let rec maybe_find f = function
    | [] -> None
    | x::l when f x -> Some x
    | x::l -> maybe_find f l

let enumerate l =
    let i = ref (-1) in
    List.map (fun x -> incr i; (!i, x)) l
