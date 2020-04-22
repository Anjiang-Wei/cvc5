#!/usr/bin/env python3

import collections
import requests
import os

Finding = collections.namedtuple("Finding", ["line", "text"])

def report_github_status(repo, token, sha, findings):
    url = "https://api.github.com/repos/{}/check-runs".format(repo)
    annotations = []
    for path, findings in findings.items():
        for f in findings:
            annotations.append({
                'path': path,
                'annotation_level': 'warning',
                'start_line': f.line,
                'end_line': f.line,
                'message': f.text
            })

    data = {
        'name': 'clang-tidy',
        'head_sha': sha,
        'status': 'completed',
        'conclusion': 'neutral',
        'output': {
            'title': 'clang-tidy',
            'summary': 'Found {} items'.format(len(annotations)),
            'annotations': annotations
        }
    }

    headers = {
        'Content-Type': 'application/json',
        'Accept': 'application/vnd.github.antiope-preview+json',
        'Authorization': 'Bearer {}'.format(token),
    }

    r = requests.post(url, json=data, headers=headers)
    print(r)
    print(r.text)


def main():
    findings = {
            'CMakeLists.txt': [Finding(5, 'foobar')]
            }

    if 'GITHUB_TOKEN' in os.environ:
        repo = os.environ['GITHUB_REPOSITORY']
        sha = os.environ['GITHUB_SHA']
        token = os.environ['GITHUB_TOKEN']
        report_github_status(repo, token, sha, findings)


if __name__ == '__main__':
    main()
