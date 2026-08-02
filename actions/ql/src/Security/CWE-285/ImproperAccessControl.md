## Overview

An authorization check may be present without preventing an untrusted actor from reaching a privileged checkout. For example, a condition may have an alternative branch that bypasses an actor or repository check, or a permission action may report insufficient access without failing the job. Low permission thresholds, unsupported enforcement options, and `continue-on-error` can have the same effect.

## Recommendation

Require authorization on every path that can reach the privileged checkout. Configure permission checks to require `write` or `admin` access and fail closed when access is missing. Do not ignore a permission action's result or allow an authorization failure to continue, and use an action version that supports the selected enforcement option.

## Example

### Incorrect Usage

The following workflow checks the triggering actor's permission, but it does not enforce the action's `require-result` output. The checkout therefore runs even when the actor lacks write access.

```yaml
on:
  pull_request_target:

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - id: permission
        uses: actions-cool/check-user-permission@v2
        with:
          require: write
      - uses: actions/checkout@v4
        with:
          repository: ${{ github.event.pull_request.head.repo.full_name }}
          ref: ${{ github.event.pull_request.head.sha }}
      - run: ./cmd
```

### Correct Usage

Fail the job when the permission action reports that the actor does not meet the required threshold.

```yaml
on:
  pull_request_target:

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - id: permission
        uses: actions-cool/check-user-permission@v2
        with:
          require: write
      - if: steps.permission.outputs.require-result == 'false'
        run: exit 1
      - uses: actions/checkout@v4
        with:
          repository: ${{ github.event.pull_request.head.repo.full_name }}
          ref: ${{ github.event.pull_request.head.sha }}
      - run: ./cmd
```

## References

- GitHub Docs: [Evaluate expressions in workflows and actions](https://docs.github.com/en/actions/reference/workflows-and-actions/expressions).
- GitHub Docs: [Workflow syntax for `continue-on-error`](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#jobsjob_idstepscontinue-on-error).
