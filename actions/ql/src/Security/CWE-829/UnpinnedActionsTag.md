## Overview

Using a tag for a third-party Action or reusable workflow that is not pinned to a commit can lead to executing untrusted code through a supply chain attack. Reusable workflows automatically receive a `GITHUB_TOKEN`, and the impact is greater when they also receive named secrets or use `secrets: inherit`.

## Recommendation

Pin third-party actions and reusable workflows to a full-length commit SHA. Pinning to a particular SHA helps mitigate the risk of a bad actor adding a backdoor to the referenced repository, as they would need to generate a SHA-1 collision for a valid Git object payload. When selecting a SHA, verify that it comes from the original repository and not a fork.

## Example

### Incorrect Usage

```yaml
- uses: tj-actions/changed-files@v44
```

```yaml
jobs:
  build:
    uses: third-party/workflows/.github/workflows/build.yml@main
```

### Correct Usage

```yaml
- uses: tj-actions/changed-files@c65cd883420fd2eb864698a825fc4162dd94482c # v44
```

```yaml
jobs:
  build:
    uses: third-party/workflows/.github/workflows/build.yml@25b062c917b0c75f8b47d8469aff6c94ffd89abb
```

## References

- GitHub Docs: [Using third-party actions](https://docs.github.com/en/actions/security-for-github-actions/security-guides/security-hardening-for-github-actions#using-third-party-actions).
- GitHub Docs: [Reusing workflow configurations](https://docs.github.com/en/actions/reference/workflows-and-actions/reusing-workflow-configurations#reusable-workflows).
