import LeanCodePrompts.NearestEmbeddings
import LeanCodePrompts.EpsilonClusters
import LeanAide.Aides
import Lean.Data.Json
import Batteries.Util.Pickle
open Lean

unsafe def checkAndFetch (descField: String) : IO Unit := do
  let picklePath ← picklePath descField
  let picklePresent ←
    if ← picklePath.pathExists then
    logToStdErr `leanaide.translate.info s!"Pickle file already present at {picklePath}"
    try
      withUnpickle  picklePath <|
        fun (_ : EmbedData) => do
        pure true
    catch e =>
        logToStdErr `leanaide.translate.info s!"Error unpickling {picklePath}: {e}"
        pure false
     else pure false
  unless picklePresent do
    logToStdErr `leanaide.translate.info s!"Fetching embeddings ... ({picklePath})"
    let out ← IO.Process.output {cmd:= "curl", args := #["--output", picklePath.toString,   "https://storage.googleapis.com/leanaide_data/{picklePath.fileName.get!}"]}
    logToStdErr `leanaide.translate.info "Fetched embeddings"
    logToStdErr `leanaide.translate.info out.stdout

def pickEmbed (data: EmbedData) : IO <| Array Float := do
  let embs := data.map fun (_, d) => d.data
  let k ← IO.rand 0 (embs.size - 1)
  pure embs[k]!

def dist (v₁ v₂ : (String × String × Bool × String) ×  FloatArray) :
  Float := distL2Sq v₁.snd v₂.snd.data

-- hack
instance : BEq ((String × String × Bool × String) × FloatArray) :=
  ⟨fun x y => x.fst = y.fst⟩

unsafe def main : IO Unit := do
  let descField := "concise-description"
  checkAndFetch descField
  let num := 25
  let picklePath ← picklePath descField
  withUnpickle  picklePath <|
    fun (data : EmbedData) => do
    let doc ←  pickEmbed data
    logToStdErr `leanaide.translate.info "Finding nearest embeddings without clustering"
    let start ← IO.monoMsNow
    let embs ← nearestDocsToDocFullEmbeddingConc data doc num (penalty := 1.0)
    let finish ← IO.monoMsNow
    logToStdErr `leanaide.translate.info s!"Found nearest in {finish - start} ms"
    let out :=
        embs.toArray.map fun (_, _, _, name, _) => name
    IO.println out
    logToStdErr `leanaide.translate.info "Finding nearest embeddings with smaller vectors"
    let start ← IO.monoMsNow
    let embs ← nearestDocsToDocFullEmbeddingConc data doc[:256] num (penalty := 1.0)
    let finish ← IO.monoMsNow
    logToStdErr `leanaide.translate.info s!"Found nearest in {finish - start} ms"
    let out :=
        embs.toArray.map fun (_, _, _, name, _) => name
    IO.println out

    -- let ε := 0.3
    -- let minSize := 50
    -- logToStdErr `leanaide.translate.info "Finding nearest embeddings with clustering"
    -- logToStdErr `leanaide.translate.info "Clustering embeddings"
    -- let clusters ←  epsilonClusters ε  dist minSize data
    -- logToStdErr `leanaide.translate.info s!"Found {clusters.size} clusters"
    -- logToStdErr `leanaide.translate.info "Finding nearest embeddings"
    -- let start ← IO.monoMsNow
    -- let embs ← Cluster.kNearest num clusters doc
    --               fun (_, d) e => distL2Sq d e
    -- let finish ← IO.monoMsNow
    -- logToStdErr `leanaide.translate.info s!"Found nearest in {finish - start} ms"
    -- let out :=
    --     embs.map fun (((_, _, _, name), _), _) => name
    -- IO.println out
