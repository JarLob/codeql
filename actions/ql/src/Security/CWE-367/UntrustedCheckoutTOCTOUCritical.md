## Overview

Untrusted Checkout is protected by a security check but the checked-out branch can be changed after the check.

## Recommendation

Verify that the code has not been modified after the security check. This may be achieved differently depending on the type of check:

- Deployment Environment Approval: Make sure to use a non-mutable reference to the code to be executed. For example use a `sha` instead of a `ref`.
- Label Gates: Use an immutable SHA and trigger the privileged run when the label is applied. A label retained across `synchronize` or `reopened` can authorize a new SHA that was never reviewed.
- IssueOps Comment Approval: The `issue_comment` payload does not contain the pull request head SHA. Capture the head SHA before checking that the pull request was not pushed to after the comment, then execute that exact captured commit. If execution happens in a dependent job, pass the captured SHA through a job output. Resolving a new SHA after the check or checking out a mutable reference remains unsafe.
- Manual Dispatch Approval: Pass the reviewed commit SHA as a `workflow_dispatch` input and check out that exact value. Passing only a pull request number leaves a mutable pull request ref, while resolving its current SHA after dispatch does not bind the approval to the reviewed revision.

## Example

### Incorrect Usage (Deployment Environment Approval)

The following workflow uses a Deployment Environment which may be configured to require an approval. However, it check outs the code pointed to by the Pull Request branch reference. At attacker could submit legitimate code for review and then change it once it gets approved.

```yml
on:
  pull_request_target:
    types: [Created]
jobs:
  test:
    environment: NeedsApproval
    runs-on: ubuntu-latest
    steps:
      - name: Checkout from PR branch
        uses: actions/checkout@v4
        with:
          repository: ${{ github.event.pull_request.head.repo.full_name }}
          ref: ${{ github.event.pull_request.head.ref }}
      - run: ./cmd
```

### Correct Usage (Deployment Environment Approval)

Use immutable references (Commit SHA) to make sure that the reviewed code does not change between the check and the use.

```yml
on:
  pull_request_target:
    types: [Created]
jobs:
  test:
    environment: NeedsApproval
    runs-on: ubuntu-latest
    steps:
      - name: Checkout from PR branch
        uses: actions/checkout@v4
        with:
          repository: ${{ github.event.pull_request.head.repo.full_name }}
          ref: ${{ github.event.pull_request.head.sha }}
      - run: ./cmd
```

### Incorrect Usage (Label Gates)

The following workflow uses a Deployment Environment which may be configured to require an approval. However, it check outs the code pointed to by the Pull Request branch reference. At attacker could submit legitimate code for review and then change it once it gets approved.

```yaml
on:
  pull_request_target:
    types: [labeled]

jobs:
  test:
    runs-on: ubuntu-latest
    if: contains(github.event.pull_request.labels.*.name, 'safe-to-test')
    steps:
      - uses: actions/checkout@v4
        with:
          ref: ${{ github.event.pull_request.head.ref }}
          repository: ${{ github.event.pull_request.head.repo.full_name }}
      - run: ./cmd
```

### Correct Usage (Label Gates)

Use immutable references (Commit SHA) to make sure that the reviewed code does not change between the check and the use.

```yaml
on:
  pull_request_target:
    types: [labeled]

jobs:
  test:
    runs-on: ubuntu-latest
    if: contains(github.event.pull_request.labels.*.name, 'safe-to-test')
    steps:
      - uses: actions/checkout@v4
        with:
          ref: ${{ github.event.pull_request.head.sha }}
          repository: ${{ github.event.pull_request.head.repo.full_name }}
      - run: ./cmd
```

### Incorrect Usage (Retained Label Approval)

An immutable SHA does not help when a persistent label is reused by a later `synchronize` or `reopened` event. The event's head SHA can identify code that was pushed after the label was approved.

```yaml
on:
  pull_request_target:
    types: [opened, labeled, synchronize, reopened]

jobs:
  test:
    runs-on: ubuntu-latest
    if: contains(github.event.pull_request.labels.*.name, 'safe-to-test')
    steps:
      - uses: actions/checkout@v4
        with:
          ref: ${{ github.event.pull_request.head.sha }}
      - run: ./cmd
```

Trigger on `labeled` as in the preceding correct example, or otherwise bind approval to the exact commit that was reviewed.

## References

- [ActionsTOCTOU](https://github.com/AdnaneKhan/ActionsTOCTOU).
