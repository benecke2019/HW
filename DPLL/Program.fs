module DPLL

open System
open System.IO

// literal: positive or negative integer(ex. 1, -2)
type Literal = int
// Clause: list of literals(ex. [1; -2; 3])
type Clause = Literal list
// CNF: list of clauses(ex. [[1; -2]; [-1; 2; 3]])
type CNF = Clause list
// Assignment: mapping variable to value(ex. {1 -> true; 2 -> false})
type Assignment = Map<int, bool>

let randEllemt (lst: 'a list) : 'a =
    let rnd = Random()
    let idx = rnd.Next(List.length lst)
    List.item idx lst

// DIMACS file parser
let parseDimacs (lines: seq<string>) : int * CNF =
    // remove comments
    let content = 
        lines 
        |> Seq.filter (fun line -> not (line.StartsWith("c") || String.IsNullOrWhiteSpace(line)))
        |> Seq.filter (fun line -> not (line.StartsWith("%")))  // for some SAT instances
        |> Seq.filter (fun line -> not (line.StartsWith("0")))   // for some SAT instances
        |> Seq.toList  // convert to list

    // seperate header and clauses
    let header, clauseLines = 
        content |> List.partition (fun line -> line.StartsWith("p"))  

    // parse header
    let (numVars, _) =
        match header with
        | firstLine :: _ -> 
            let parts = firstLine.Split([|' '|], StringSplitOptions.RemoveEmptyEntries)
            if parts.Length >= 4 then (int parts.[2], int parts.[3])
            else failwith "Invalid header in DIMACS file"
        | [] -> failwith "No header line found in DIMACS file"

    // parse clauses
    let clauses =
        clauseLines
        |> List.map (fun line ->
            line.Split([|' '|], StringSplitOptions.RemoveEmptyEntries)
            |> Array.map int
            |> Array.toList
            |> List.takeWhile (fun lit -> lit <> 0)
        )

    (numVars, clauses)

// read DIMACS file and call parser
let readDimacs path =
    let lines = File.ReadLines(path)
    parseDimacs lines


// assign var with vlaue and remove opposite literal
let assignLiteral (formula: CNF) (var: int) (value: bool) : CNF =
    let lit = if value then var else -var   
    let newFormula =
        formula 
        |> List.choose (fun clause ->
        if List.contains lit clause then
            None                            // remove clause
        else                                // remove opposite literal
            let newClause = clause |> List.filter (fun l -> l <> -lit)
            Some newClause
    )
    if List.exists (fun clause -> clause = []) newFormula then
        [[]]  // contradiction
    else 
        newFormula

// BCP(Boolean Constraint Propagation) implementation
let rec unitPropagation (formula: CNF, assignment: Assignment) : (CNF * Assignment) option =
    // collect all unit clauses(only one literal)
    let unitClauses: Clause list = formula |> List.filter (fun clause -> clause.Length = 1)
    if unitClauses.IsEmpty then Some(formula, assignment)       // no unit clause
    else
        let folder state unitClause =   // folder(state, unitClause) -> (formula, Assignment)
            match state with
            | None -> None
            | Some (form, assign) ->
                let unitVal = List.head unitClause  // get unit literal
                let var = abs unitVal               // get var name
                let value = unitVal > 0             // get value
                // contradiction check
                match Map.tryFind var assign with
                | Some existing when existing <> value -> None  // conflict
                | _ ->
                    let newAssign = assign.Add(var, value)          // update assignment
                    let newForm = assignLiteral form var value      // update formula
                    unitPropagation (newForm, newAssign)            // recursive call

        unitClauses |> List.fold folder (Some(formula, assignment)) // start BCP

/// PLE(Pure Literal Elimination) implementation
let pureLiteralElimination (formula: CNF, assignment: Assignment) : (CNF * Assignment) =
    let allLits = List.concat formula
    let pureAssignments: (int * bool) list =
        allLits
        |> List.map abs             // get variable name
        |> List.distinct            // remove duplicates
        |> List.choose (fun v ->    // for each variable
            let pos = allLits |> List.exists (fun l -> l = v)
            let neg = allLits |> List.exists (fun l -> l = -v)
            match (pos, neg) with
            | (true, false) -> Some (v, true)   // var only has positive value(Pos)
            | (false, true) -> Some (v, false)  // var only has negative value(Neg)
            | _ -> None                         // var has both positive and negative values
        )
    
    let newAssignment = // update assignment based on pure literals(v, b)
        pureAssignments |> List.fold (fun (acc: Assignment) (v, b) -> acc.Add(v, b)) assignment
    let newFormula =    // update formula based on pure literals(v, b)
        pureAssignments |> List.fold (fun form (v, b) -> assignLiteral form v b) formula
    (newFormula, newAssignment)


/// DPLL algorithm 
let rec dpll (formula: CNF) (assignment: Assignment) (numVars: int) : Assignment option =
    match unitPropagation (formula, assignment) with                                    // try BCP
    | None -> None      // found contradiction
    | Some (formula1, assignment1) ->
        let (formula2, assignment2) = pureLiteralElimination (formula1, assignment1)    // try PLE
        if formula2.IsEmpty then Some assignment2                               // found solution
        elif formula2 |> List.exists (fun clause -> clause.IsEmpty) then None   // found contradiction
        else            // try DPLL with random variable
            let allAssigned = assignment2 |> Map.toList |> List.map fst |> Set.ofList   // get assigned variables
            let allVars = Set.ofList [1..numVars]                                       // get all variables 
            let unassigned = Set.difference allVars allAssigned |> Set.toList   // get unassigned variables
            if unassigned.IsEmpty then Some assignment2                         // all variables are assigned
            else
                //let var = List.head unassigned  // for all unassigned variables(lexicographic order)
                let var = randEllemt unassigned   // for all unassigned variables(random order)
                let tryTrue = dpll (assignLiteral formula2 var true) (assignment2.Add(var, true)) numVars   // first try with true
                match tryTrue with
                | Some sol -> Some sol
                | None -> dpll (assignLiteral formula2 var false) (assignment2.Add(var, false)) numVars     // then try with false


// Main entry point
[<EntryPoint>]
let main argv =
    if argv.Length <> 1 then
        printfn "Usage: SATSolver <input-file>"
        1
    else
        let filePath = argv.[0]
        try
            // read DIMACS file
            let (numVars, formula) = readDimacs filePath
            // run DPLL algorithm
            match dpll formula Map.empty numVars with
            // print result
            | Some solution ->
                printfn "SAT"
                for v in 1 .. numVars do
                    let value = 
                        match solution.TryFind v with
                        | Some b -> b
                        | None -> false
                    printfn "Variable %d = %b" v value
            | None ->
                printfn "UNSAT"
            0
        with ex ->  // exception handling
            printfn "Error: %s" ex.Message
            1
