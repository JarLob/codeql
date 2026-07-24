## Overview

When the workflow runner cannot determine what secrets are needed, it receives all available organization and repository secrets. Calling a reusable workflow with `secrets: inherit` similarly makes every available secret accessible to that workflow. Both patterns violate least privilege and increase the impact of a compromised runner or reusable workflow.

## Recommendation

Only pass the secrets needed by the job or reusable workflow. Avoid expressions such as `toJSON(secrets)`, dynamically accessed secrets such as `secrets[format('GH_PAT_%s', matrix.env)]`, and `secrets: inherit`. Prefer explicit named secret mappings for reusable workflows.

## Example

### Incorrect Usage

```yaml
env:
  ALL_SECRETS: ${{ toJSON(secrets) }}
```

```yaml
strategy:
  matrix:
    env: [PROD, DEV]
env:
  GH_TOKEN: ${{ secrets[format('GH_PAT_%s', matrix.env)] }}
```

```yaml
jobs:
  build:
    uses: octo-org/example/.github/workflows/build.yml@main
    secrets: inherit
```

### Correct Usage

```yaml
env:
  NEEDED_SECRET: ${{ secrets.GH_PAT }}
```

```yaml
strategy:
  matrix:
    env: [PROD, DEV]
---
if: matrix.env == "PROD"
env:
  GH_TOKEN: ${{ secrets.GH_PAT_PROD }}
---
if: matrix.env == "DEV"
env:
  GH_TOKEN: ${{ secrets.GH_PAT_DEV }}
```

```yaml
jobs:
  build:
    uses: octo-org/example/.github/workflows/build.yml@25b062c917b0c75f8b47d8469aff6c94ffd89abb
    secrets:
      token: ${{ secrets.GH_PAT }}
```

## References

- GitHub Docs: [Using secrets in GitHub Actions](https://docs.github.com/en/actions/security-for-github-actions/security-guides/using-secrets-in-github-actions#using-encrypted-secrets-in-a-workflow).
- poutine: [Job uses all secrets](https://github.com/boostsecurityio/poutine/blob/main/docs/content/en/rules/job_all_secrets.md).
