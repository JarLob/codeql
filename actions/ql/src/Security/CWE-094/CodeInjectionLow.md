## Overview

Using user-controlled input in GitHub Actions expressions may lead to code injection. Workflows
triggered by `pull_request` are isolated from repository write permissions and secrets for fork pull
requests, which limits the impact but does not prevent arbitrary code execution in the workflow.

## Recommendation

Assign untrusted expression values to environment variables and read them using the native syntax
of the shell or script interpreter instead of interpolating them directly into generated code.

## Example

### Incorrect Usage

```yaml
on: pull_request

jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - run: echo '${{ github.event.pull_request.title }}'
```

### Correct Usage

```yaml
on: pull_request

jobs:
  check:
    runs-on: ubuntu-latest
    steps:
      - env:
          TITLE: ${{ github.event.pull_request.title }}
        run: echo "$TITLE"
```

## References

- GitHub Security Lab Research: [Keeping your GitHub Actions and workflows secure: Untrusted input](https://securitylab.github.com/research/github-actions-untrusted-input).
- GitHub Docs: [Security hardening for GitHub Actions](https://docs.github.com/en/actions/security-guides/security-hardening-for-github-actions).