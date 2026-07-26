## Overview

Using user-controlled input in GitHub Actions may lead to code injection in contexts like _run:_, _script:_, or a job container image. A job container supplies the shell and other binaries used to execute the job's steps. If an attacker controls the complete image name, they can select an image containing malicious replacements for those binaries and capture credentials explicitly passed to a step.

Code injection in GitHub Actions may allow an attacker to exfiltrate secrets used in the workflow and the temporary GitHub repository authorization token. For attacker-selected job containers, this query requires evidence that the job exposes a named secret or a write-capable GitHub token. A token permission declaration alone does not expose the token to the container.

## Recommendation

The best practice to avoid code injection vulnerabilities in GitHub workflows is to set the untrusted input value of the expression to an intermediate environment variable and then use the environment variable using the native syntax of the shell/script interpreter (that is, not _${{ env.VAR }}_).

For job containers, use a fixed image, preferably pinned by digest. If a workflow must select from multiple images, map the input to a strict allowlist of complete image references. Do not use untrusted event data as the complete image name.

It is also recommended to limit the permissions of any tokens used by a workflow such as the GITHUB_TOKEN.

## Example

### Incorrect Usage

The following example lets attackers inject an arbitrary shell command:

```yaml
on: issue_comment

jobs:
  echo-body:
    runs-on: ubuntu-latest
    steps:
      - run: |
          echo '${{ github.event.comment.body }}'
```

The following example uses an environment variable, but **still allows the injection** because of the use of expression syntax:

```yaml
on: issue_comment

jobs:
  echo-body:
    runs-on: ubuntu-latest
    steps:
    -  env:
        BODY: ${{ github.event.issue.body }}
      run: |
        echo '${{ env.BODY }}'
```

The following privileged workflow lets a pull request author select the job container image through the pull request title. The step explicitly passes the write-capable GitHub token into the attacker-selected container:

```yaml
on: pull_request_target

jobs:
  test:
    permissions:
      contents: write
    runs-on: ubuntu-latest
    container:
      image: ${{ github.event.pull_request.title }}
    steps:
      - env:
          GH_TOKEN: ${{ github.token }}
        run: npm test
```

### Correct Usage

The following example uses shell syntax to read the environment variable and will prevent the attack:

```yaml
jobs:
  echo-body:
    runs-on: ubuntu-latest
    steps:
      - env:
          BODY: ${{ github.event.issue.body }}
        run: |
          echo "$BODY"
```

The following example uses `process.env` to read environment variables within JavaScript code.

```yaml
jobs:
  echo-body:
    runs-on: ubuntu-latest
    steps:
      - uses: uses: actions/github-script@v4
        env:
          BODY: ${{ github.event.issue.body }}
        with:
          script: |
            const { BODY } = process.env
            ...
```

The following example uses a fixed, digest-pinned job container image:

```yaml
jobs:
  test:
    permissions:
      contents: read
    runs-on: ubuntu-latest
    container:
      image: node@sha256:0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef
    steps:
      - run: npm test
```

## References

- GitHub Security Lab Research: [Keeping your GitHub Actions and workflows secure: Untrusted input](https://securitylab.github.com/research/github-actions-untrusted-input).
- GitHub Docs: [Security hardening for GitHub Actions](https://docs.github.com/en/actions/security-guides/security-hardening-for-github-actions).
- GitHub Docs: [Permissions for the GITHUB_TOKEN](https://docs.github.com/en/actions/security-guides/automatic-token-authentication#permissions-for-the-github_token).
- GitHub Docs: [Running jobs in a container](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#jobsjob_idcontainer).
