module DPLL

open System
open System.IO

// -----------------------------------------
// 자료구조 정의
// -----------------------------------------

/// 리터럴: 양의 정수는 해당 변수, 음의 정수는 부정을 의미.
type Literal = int

/// 절: 리터럴의 리스트
type Clause = Literal list

/// CNF 포뮬러: 절들의 리스트
type CNF = Clause list

/// 변수 할당: 변수 번호와 그에 대응하는 Boolean 값의 매핑
type Assignment = Map<int, bool>

// -----------------------------------------
// DIMACS 파일 파싱
// -----------------------------------------

/// DIMACS 파일의 모든 라인을 파싱하여 (변수 개수, CNF 포뮬러)를 반환한다.
let parseDimacs (lines: seq<string>) : int * CNF =
    // 주석(c)와 빈 줄 제거
    let content = 
        lines 
        |> Seq.filter (fun line -> not (line.StartsWith("c") || String.IsNullOrWhiteSpace(line)))
        |> Seq.toList  // 추가: 리스트로 변환하여 `List.partition` 사용 가능하게 함

    // header와 나머지 절 라인 분리 (header는 "p cnf <numVars> <numClauses>" 형식)
    let header, clauseLines = 
        content |> List.partition (fun line -> line.StartsWith("p"))  // ✅ 수정 완료

    let (numVars, _) =
        match header with
        | firstLine :: _ -> 
            let parts = firstLine.Split([|' '|], StringSplitOptions.RemoveEmptyEntries)
            if parts.Length >= 4 then (int parts.[2], int parts.[3])
            else failwith "Invalid header in DIMACS file"
        | [] -> failwith "No header line found in DIMACS file"

    // 절 파싱: 각 절은 마지막 0을 제외한 리터럴들의 리스트임
    let clauses =
        clauseLines
        |> List.map (fun line ->
            line.Split([|' '|], StringSplitOptions.RemoveEmptyEntries)
            |> Array.map int
            |> Array.toList
            |> List.takeWhile (fun lit -> lit <> 0)
        )

    (numVars, clauses)

/// 지정된 경로의 DIMACS 파일을 읽어 파싱한다.
let readDimacs path =
    let lines = File.ReadLines(path)
    parseDimacs lines

// -----------------------------------------
// 유틸리티 함수: 할당 적용, 단위 전파, 순수 리터럴 제거 등
// -----------------------------------------

/// 변수 var에 대해 value를 할당한 결과, CNF에서 해당 할당이
/// 만족하는 절은 제거하고, 반대쪽 리터럴은 삭제하여 CNF를 갱신한다.
let assignLiteral (formula: CNF) (var: int) (value: bool) : CNF =
    let lit = if value then var else -var
    formula
    |> List.choose (fun clause ->
        if List.contains lit clause then
            // 이 절은 할당으로 만족되었으므로 제거
            None
        else
            // 반대쪽 리터럴은 제거
            let newClause = clause |> List.filter (fun l -> l <> -lit)
            Some newClause
    )

/// 단위 전파: 단위 절이 존재하면 해당 리터럴에 대해 할당을 적용하고, 변경된 CNF와 할당을 반환.
/// 충돌이 발생하면 None을 반환한다.
let rec unitPropagation (formula: CNF, assignment: Assignment) : (CNF * Assignment) option =
    // 단위 절: 길이가 1인 절
    let unitClauses: Clause list = formula |> List.filter (fun clause -> clause.Length = 1)
    if unitClauses.IsEmpty then Some(formula, assignment)
    else
        // 모든 단위 절에 대해 전파를 수행한다.
        let folder state unitClause =
            match state with
            | None -> None
            | Some (form, assign) ->
                let unitVal = List.head unitClause
                let var = abs unitVal
                let value = unitVal > 0
                // 모순: 이미 다른 값으로 할당되어 있으면 실패
                match Map.tryFind var assign with
                | Some existing when existing <> value -> None
                | _ ->
                    let newAssign = assign.Add(var, value)
                    let newForm = assignLiteral form var value
                    unitPropagation (newForm, newAssign)
        unitClauses |> List.fold folder (Some(formula, assignment))

/// 순수 리터럴 제거: CNF 내에서 한쪽(양/음)만 등장하는 리터럴에 대해 할당을 적용한다.
let pureLiteralElimination (formula: CNF, assignment: Assignment) : (CNF * Assignment) =
    // 모든 리터럴 수집
    let allLits = List.concat formula
    // 변수별로 등장하는 양/음 리터럴 여부를 조사
    let pureAssignments: (int * bool) list =
        allLits
        |> List.map abs
        |> List.distinct
        |> List.choose (fun v ->
            let pos = allLits |> List.exists (fun l -> l = v)
            let neg = allLits |> List.exists (fun l -> l = -v)
            match (pos, neg) with
            | (true, false) -> Some (v, true)
            | (false, true) -> Some (v, false)
            | _ -> None
        )
    // 할당 및 CNF 갱신
    let newAssignment =
        pureAssignments |> List.fold (fun (acc: Assignment) (v, b) -> acc.Add(v, b)) assignment
    let newFormula =
        pureAssignments |> List.fold (fun form (v, b) -> assignLiteral form v b) formula
    (newFormula, newAssignment)

// -----------------------------------------
// DPLL 재귀 알고리즘 (완전한 SAT 솔버)
// -----------------------------------------

/// DPLL 함수: CNF와 현재 할당을 받아, 만족하는 할당(Assignment)을 Some으로, 불만족이면 None을 반환.
let rec dpll (formula: CNF) (assignment: Assignment) (numVars: int) : Assignment option =
    // 먼저 단위 전파를 수행
    match unitPropagation (formula, assignment) with
    | None -> None  // 충돌 발생
    | Some (formula1, assignment1) ->
        // 순수 리터럴 제거 적용
        let (formula2, assignment2) = pureLiteralElimination (formula1, assignment1)
        // 모든 절이 제거되었다면 모두 만족된 것이므로 해답 반환
        if formula2.IsEmpty then Some assignment2
        // 충돌: 빈 절이 존재하면 현재 경로는 실패
        elif formula2 |> List.exists (fun clause -> clause.IsEmpty) then None
        else
            // 아직 결정되지 않은 변수가 남아있으므로 하나를 선택하여 분기
            let allAssigned = assignment2 |> Map.toList |> List.map fst |> Set.ofList
            let allVars = Set.ofList [1..numVars]
            let unassigned = Set.difference allVars allAssigned |> Set.toList
            if unassigned.IsEmpty then Some assignment2
            else
                let var = List.head unassigned
                // true/false 할당 시도
                let tryTrue = dpll (assignLiteral formula2 var true) (assignment2.Add(var, true)) numVars
                match tryTrue with
                | Some sol -> Some sol
                | None -> dpll (assignLiteral formula2 var false) (assignment2.Add(var, false)) numVars

// -----------------------------------------
// 메인 프로그램: DIMACS 파일 입력 및 결과 출력
// -----------------------------------------

[<EntryPoint>]
let main argv =
    if argv.Length <> 1 then
        printfn "Usage: SATSolver <input-file>"
        1
    else
        let filePath = argv.[0]
        try
            let (numVars, formula) = readDimacs filePath
            match dpll formula Map.empty numVars with
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
        with ex ->
            printfn "Error: %s" ex.Message
            1
