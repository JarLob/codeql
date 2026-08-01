## Overview

Sometimes labels are used to approve GitHub Actions. An authorization check may not be properly implemented, allowing an attacker to mutate the code after it has been reviewed and approved by label. Because labels belong to a pull request rather than a particular commit, later workflow runs may reuse an approval for different code.

## Recommendation

When using labels, trigger the privileged workflow only when the approval label is applied and check out the approved commit by its immutable SHA.

## Example

### Incorrect Usage

The following example shows a job that requires the label `safe to test` to be set before running untrusted code. There are three problems with the code:

1. The workflow gets triggered on the `synchronize` activity type and, therefore, it will run every time the pull request head changes. An attacker can modify the pull request after it has been reviewed and labeled, and the existing label will authorize the new commit.
2. The `reopened` activity type creates a similar path: an attacker can close the labeled pull request, update its branch, and reopen it while retaining the approval label.
3. The workflow uses `ref: ${{ github.event.pull_request.head.ref }}` for checkout, which is a mutable branch name. There is a window of opportunity for the attacker to modify their branch after the pull request is labeled but before the workflow checks it out.

```yaml
on:
  pull_request_target:
    types: [opened, synchronize, reopened]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - name: Checkout repo for OWNER TEST
        uses: actions/checkout@v3
        if: contains(github.event.pull_request.labels.*.name, 'safe to test')
        with:
          ref: ${{ github.event.pull_request.head.ref }}
      - run: ./cmd
```

### Correct Usage

Make sure that the workflow only gets triggered when the label is set and use an immutable commit (`github.event.pull_request.head.sha`) instead of a mutable reference.

```yaml
on:
  pull_request_target:
    types: [labeled]

jobs:
  test:
    runs-on: ubuntu-latest
    steps:
      - name: Checkout repo for OWNER TEST
        uses: actions/checkout@v3
        if: contains(github.event.pull_request.labels.*.name, 'safe to test')
        with:
          ref: ${{ github.event.pull_request.head.sha}}
      - run: ./cmd
```

## References

- GitHub Docs: [Events that trigger workflows](https://docs.github.com/en/actions/writing-workflows/choosing-when-your-workflow-runs/events-that-trigger-workflows#pull_request_target).
