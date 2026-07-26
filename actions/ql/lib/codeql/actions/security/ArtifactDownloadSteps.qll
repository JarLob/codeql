private import actions

abstract class UntrustedArtifactDownloadStep extends Step {
  abstract string getPath();
}