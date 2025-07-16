import Lean.Data.Json
import ServiceMetrics

open Lean Json ToJson ServiceMetrics

deriving instance FromJson for Operation
deriving instance FromJson for Service
deriving instance FromJson for Call

structure Genotype where
  microservices : List Service
  calls         : List Call
  deriving FromJson, Repr

/--
  Empaqueta en JSON las métricas:
    - lcom_avg      = media de LCOM
    - sgm_max       = máximo de SGM
    - sgm_sd_sum    = suma de sgmSd
    - coupling_max  = máximo de couplingOut
  Redondeo a 3 decimales.
-/
def reportMetrics (gt : Genotype) : Json :=
  let svcs      := gt.microservices
  let n         := svcs.length
  let lcoms     := svcs.map LCOM
  let sgms      := svcs.map SGM
  let sds       := svcs.map sgmSd
  let cps       := svcs.map (fun s => couplingOut s.name gt.calls)
  let lcomAvg   := if n == 0 then 0.0 else (lcoms.foldl (· + ·) 0.0) / (n.toFloat)
  let sgmMax    := sgms.foldl (fun a b => if a >= b then a else b) 0.0
  let sgmSdSum  := sds.foldl (· + ·) 0.0
  let coupMax   := cps.foldl Nat.max 0
  let round3 (x : Float) : Float := Float.round (x * 1000.0) / 1000.0
  Json.mkObj [
    ("lcom_avg",     toJson (round3 lcomAvg)),
    ("sgm_max",      toJson (round3 sgmMax)),
    ("sgm_sd_sum",   toJson (round3 sgmSdSum)),
    ("coupling_max", toJson coupMax)
  ]

/--
  Solo valida referencias básicas y estructura.
  Ya NO aborta por métricas malas (deja que el evolutivo lo penalice).
  Solo retorna error si el JSON es inválido o la estructura está rota.
-/
def validateGenotype (gt : Genotype) : Except String Unit := do
  let names := gt.microservices.map (·.name)
  for c in gt.calls do
    if c.caller == c.callee then throw s!"Self-call: {c.caller}"
    unless names.contains c.caller do throw s!"Unknown caller: {c.caller}"
    unless names.contains c.callee do throw s!"Unknown callee: {c.callee}"
  pure ()

/--
  Punto de entrada: siempre imprime un único JSON con:
   • status   : "OK" o "ERROR"
   • message  : texto de error (vacío si OK)
   • metrics  : objeto con las métricas (vacío si ERROR)
-/
def main (args : List String) : IO UInt32 := do
  if args.length != 1 then
    IO.eprintln "Uso: lake exe validate <ruta_al_genotipo.json>"
    return 1
  let filePath := args.head!
  let content  ← IO.FS.readFile filePath
  match Json.parse content >>= fromJson? (α := Genotype) with
  | Except.error err =>
    let out := Json.mkObj [
      ("status",  Json.str "ERROR"),
      ("message", Json.str s!"JSON parse error: {err}"),
      ("metrics", Json.mkObj [])
    ]
    IO.println (toString out)
    return 1
  | Except.ok gt =>
    match validateGenotype gt with
    | Except.error msg =>
      let out := Json.mkObj [
        ("status",  Json.str "ERROR"),
        ("message", Json.str msg),
        ("metrics", Json.mkObj [])
      ]
      IO.println (toString out)
      return 1
    | Except.ok _ =>
      let metricsJson := reportMetrics gt
      let out := Json.mkObj [
        ("status",  Json.str "OK"),
        ("message", Json.str ""),
        ("metrics", metricsJson)
      ]
      IO.println (toString out)
      return 0
