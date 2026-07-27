private import actions

string unzipRegexp() { result = "(unzip|tar)\\s+.*" }

string unzipDirArgRegexp() { result = "(-d|-C)\\s+([^ ]+).*" }

abstract class PotentiallyUntrustedArtifactDownloadStep extends Step {
  abstract string getPath();
}

abstract class UntrustedArtifactDownloadStep extends PotentiallyUntrustedArtifactDownloadStep { }

class GitHubWorkflowRunDownloadArtifactActionStep extends UntrustedArtifactDownloadStep, UsesStep {
  GitHubWorkflowRunDownloadArtifactActionStep() {
    this.getCallee() = "actions/download-artifact" and
    this.getArgument("run-id").matches("%github.event.workflow_run.id%") and
    exists(this.getArgument("github-token"))
  }

  override string getPath() {
    if exists(this.getArgument("path"))
    then result = normalizePath(this.getArgument("path"))
    else result = "GITHUB_WORKSPACE/"
  }
}

class PotentiallyCurrentWorkflowArtifactDownloadActionStep extends
    PotentiallyUntrustedArtifactDownloadStep, UsesStep
{
  PotentiallyCurrentWorkflowArtifactDownloadActionStep() {
    this.getCallee() = "actions/download-artifact" and
    exists(LocalJob job, UsesStep checkout, UsesStep upload |
      this.getEnclosingWorkflow().getAJob() = job and
      job.getAContainedStep() = checkout and
      checkout.getCallee() = "actions/checkout" and
      checkout.getATriggerEvent().getName() = "pull_request_target" and
      checkout.getArgument("ref").matches("%github.event.pull_request.head.sha%") and
      checkout.getAFollowingStep() = upload and
      upload.getCallee() = "actions/upload-artifact"
    )
  }

  override string getPath() {
    if exists(this.getArgument("path"))
    then result = normalizePath(this.getArgument("path"))
    else result = "GITHUB_WORKSPACE/"
  }
}

class DownloadArtifactActionStep extends UntrustedArtifactDownloadStep, UsesStep {
  DownloadArtifactActionStep() {
    this.getCallee() =
      [
        "dawidd6/action-download-artifact", "marcofaggian/action-download-multiple-artifacts",
        "benday-inc/download-latest-artifact", "blablacar/action-download-last-artifact",
        "levonet/action-download-last-artifact", "bettermarks/action-artifact-download",
        "aochmann/actions-download-artifact", "cytopia/download-artifact-retry-action",
        "alextompkins/download-prior-artifact", "nmerget/download-gzip-artifact",
        "benday-inc/download-artifact", "synergy-au/download-workflow-artifacts-action",
        "ishworkh/docker-image-artifact-download", "ishworkh/container-image-artifact-download",
        "sidx1024/action-download-artifact", "hyperskill/azblob-download-artifact",
        "ma-ve/action-download-artifact-with-retry"
      ] and
    (
      not exists(this.getArgument(["branch", "branch_name"]))
      or
      exists(this.getArgument(["branch", "branch_name"])) and
      this.getArgument("allow_forks") = "true"
    ) and
    (
      not exists(this.getArgument(["commit", "commitHash", "commit_sha"])) or
      not this.getArgument(["commit", "commitHash", "commit_sha"])
          .matches("%github.event.pull_request.head.sha%")
    ) and
    (
      not exists(this.getArgument("event")) or
      not this.getArgument("event") = "pull_request"
    ) and
    (
      not exists(this.getArgument(["run-id", "run_id", "workflow-run-id", "workflow_run_id"])) or
      this.getArgument(["run-id", "run_id", "workflow-run-id", "workflow_run_id"])
          .matches("%github.event.workflow_run.id%")
    ) and
    (
      not exists(this.getArgument("pr")) or
      not this.getArgument("pr")
          .matches(["%github.event.pull_request.number%", "%github.event.number%"])
    )
  }

  override string getPath() {
    if exists(this.getArgument(["path", "download_path"]))
    then result = normalizePath(this.getArgument(["path", "download_path"]))
    else
      if exists(this.getArgument("paths"))
      then result = normalizePath(this.getArgument("paths").splitAt(" "))
      else result = "GITHUB_WORKSPACE/"
  }
}

class LegitLabsDownloadArtifactActionStep extends UntrustedArtifactDownloadStep, UsesStep {
  LegitLabsDownloadArtifactActionStep() {
    this.getCallee() = "Legit-Labs/action-download-artifact" and
    (
      not exists(this.getArgument("branch")) or
      not this.getArgument("branch") = ["main", "master"]
    ) and
    (
      not exists(this.getArgument("commit")) or
      not this.getArgument("commit").matches("%github.event.pull_request.head.sha%")
    ) and
    (
      not exists(this.getArgument("event")) or
      not this.getArgument("event") = "pull_request"
    ) and
    (
      not exists(this.getArgument("run_id")) or
      not this.getArgument("run_id").matches("%github.event.workflow_run.id%")
    ) and
    (
      not exists(this.getArgument("pr")) or
      not this.getArgument("pr").matches("%github.event.pull_request.number%")
    )
  }

  override string getPath() {
    if exists(this.getArgument("path"))
    then result = normalizePath(this.getArgument("path"))
    else result = "GITHUB_WORKSPACE/artifacts"
  }
}

class ActionsGitHubScriptDownloadStep extends UntrustedArtifactDownloadStep, UsesStep {
  ActionsGitHubScriptDownloadStep() {
    this.getCallee() = "actions/github-script" and
    exists(string script |
      this.getArgument("script") = script and
      script.matches("%listWorkflowRunArtifacts(%") and
      script.matches("%downloadArtifact(%") and
      script.matches("%writeFileSync(%") and
      not script.matches("%exclude_pull_requests: true%")
    )
  }

  override string getPath() {
    if
      this.getAFollowingStep()
          .(Run)
          .getScript()
          .getACommand()
          .regexpMatch(unzipRegexp() + unzipDirArgRegexp())
    then
      result =
        normalizePath(trimQuotes(this.getAFollowingStep()
                .(Run)
                .getScript()
                .getACommand()
                .regexpCapture(unzipRegexp() + unzipDirArgRegexp(), 3)))
    else (
      this.getAFollowingStep().(Run).getScript().getACommand().regexpMatch(unzipRegexp()) and
      result = "GITHUB_WORKSPACE/"
    )
  }
}

class GHRunArtifactDownloadStep extends UntrustedArtifactDownloadStep, Run {
  GHRunArtifactDownloadStep() {
    this.getScript().getACommand().regexpMatch(".*gh\\s+run\\s+download.*") and
    (
      this.getScript().getACommand().regexpMatch(unzipRegexp()) or
      this.getAFollowingStep().(Run).getScript().getACommand().regexpMatch(unzipRegexp())
    )
  }

  override string getPath() {
    if
      this.getAFollowingStep()
          .(Run)
          .getScript()
          .getACommand()
          .regexpMatch(unzipRegexp() + unzipDirArgRegexp()) or
      this.getScript().getACommand().regexpMatch(unzipRegexp() + unzipDirArgRegexp())
    then
      result =
        normalizePath(trimQuotes(this.getScript()
                .getACommand()
                .regexpCapture(unzipRegexp() + unzipDirArgRegexp(), 3))) or
      result =
        normalizePath(trimQuotes(this.getAFollowingStep()
                .(Run)
                .getScript()
                .getACommand()
                .regexpCapture(unzipRegexp() + unzipDirArgRegexp(), 3)))
    else (
      (
        this.getAFollowingStep().(Run).getScript().getACommand().regexpMatch(unzipRegexp()) or
        this.getScript().getACommand().regexpMatch(unzipRegexp())
      ) and
      result = "GITHUB_WORKSPACE/"
    )
  }
}

class DirectArtifactDownloadStep extends UntrustedArtifactDownloadStep, Run {
  DirectArtifactDownloadStep() {
    this.getScript().getACommand().matches("%github.event.workflow_run.artifacts_url%") and
    (
      this.getScript().getACommand().regexpMatch(unzipRegexp()) or
      this.getAFollowingStep().(Run).getScript().getACommand().regexpMatch(unzipRegexp())
    )
  }

  override string getPath() {
    if
      this.getScript().getACommand().regexpMatch(unzipRegexp() + unzipDirArgRegexp()) or
      this.getAFollowingStep()
          .(Run)
          .getScript()
          .getACommand()
          .regexpMatch(unzipRegexp() + unzipDirArgRegexp())
    then
      result =
        normalizePath(trimQuotes(this.getScript()
                .getACommand()
                .regexpCapture(unzipRegexp() + unzipDirArgRegexp(), 3))) or
      result =
        normalizePath(trimQuotes(this.getAFollowingStep()
                .(Run)
                .getScript()
                .getACommand()
                .regexpCapture(unzipRegexp() + unzipDirArgRegexp(), 3)))
    else result = "GITHUB_WORKSPACE/"
  }
}