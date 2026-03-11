def print_compat_runner_module_source(
    module_name: str = "Generated.RunCompatCheck",
    old_api_module_name: str = "Generated.GeneratedOldAPI",
    new_api_module_name: str = "Generated.GeneratedNewAPI",
) -> str:
    lines = [
        f"module {module_name} where",
        "",
        "open import Agda.Builtin.IO",
        "import Agda.Builtin.Unit as Unit",
        "",
        "open import Prelude using (String; _∔_; inl; inr)",
        f"open import {old_api_module_name}",
        f"open import {new_api_module_name}",
        "open import WellFormed.Core",
        "open import WellFormed.Decidable",
        "open import WellFormed.IllFormed",
        "open import Semantics.APIRefinement",
        "open import Semantics.DecidableRefinement",
        "open import Semantics.Drift",
        "",
        "oldWF : WFAPI GeneratedAPI ∔ APIIllFormed GeneratedAPI",
        "oldWF = WFAPI? GeneratedAPI",
        "",
        "newWF : WFAPI GeneratedAPI ∔ APIIllFormed GeneratedAPI",
        "newWF = WFAPI? GeneratedAPI",
        "",
        "compatTag : String",
        "compatTag with oldWF | newWF",
        "... | inr _ | _ = \"COMPAT_CHECK_ERROR:OLD_SPEC_NOT_WF\"",
        "... | _ | inr _ = \"COMPAT_CHECK_ERROR:NEW_SPEC_NOT_WF\"",
        "... | inl wfOld | inl wfNew with API⊑? GeneratedAPI GeneratedAPI wfOld wfNew",
        "... | inl _ = \"COMPAT_OK\"",
        "... | inr (ComponentRemoved _ _) = \"COMPAT_ERR:COMPONENT_REMOVED\"",
        "... | inr (ComponentDriftWitness _ _ _) = \"COMPAT_ERR:COMPONENT_DRIFT\"",
        "... | inr (EndpointRemoved _ _) = \"COMPAT_ERR:ENDPOINT_REMOVED\"",
        "... | inr (EndpointDriftWitness _ _ _) = \"COMPAT_ERR:ENDPOINT_DRIFT\"",
        "",
        "postulate",
        "  printResult : String → String → String → String → String → IO Unit.⊤",
        "{-# FOREIGN GHC import qualified Data.Text.IO as T #-}",
        "{-# COMPILE GHC printResult = \\tag k1 v1 k2 v2 -> T.putStrLn tag >> T.putStrLn k1 >> T.putStrLn v1 >> T.putStrLn k2 >> T.putStrLn v2 >> return () #-}",
        "",
        "main : IO Unit.⊤",
        "main = printResult compatTag \"\" \"\" \"\" \"\"",
    ]

    source = "\n".join(lines)

    # The old/new generated API modules both define GeneratedAPI.
    # Rename references in imported modules by editing module qualifiers.
    source = source.replace("open import " + old_api_module_name, "open import " + old_api_module_name + " renaming (GeneratedAPI to OldAPI)")
    source = source.replace("open import " + new_api_module_name, "open import " + new_api_module_name + " renaming (GeneratedAPI to NewAPI)")
    source = source.replace("oldWF : WFAPI GeneratedAPI ∔ APIIllFormed GeneratedAPI", "oldWF : WFAPI OldAPI ∔ APIIllFormed OldAPI")
    source = source.replace("oldWF = WFAPI? GeneratedAPI", "oldWF = WFAPI? OldAPI")
    source = source.replace("newWF : WFAPI GeneratedAPI ∔ APIIllFormed GeneratedAPI", "newWF : WFAPI NewAPI ∔ APIIllFormed NewAPI")
    source = source.replace("newWF = WFAPI? GeneratedAPI", "newWF = WFAPI? NewAPI")
    source = source.replace("API⊑? GeneratedAPI GeneratedAPI", "API⊑? OldAPI NewAPI")

    return source
