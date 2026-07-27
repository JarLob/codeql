import actions
import codeql.actions.security.ArtifactDownloadSteps
import codeql.actions.security.ArtifactPoisoningQuery

query predicate classifiedDownloads(string stepId, string classification) {
  exists(Step step |
    step.getId() = stepId and
    (
      classification = "potential" and
      step instanceof PotentiallyUntrustedArtifactDownloadStep
      or
      classification = "precise" and step instanceof UntrustedArtifactDownloadStep
    )
  )
}