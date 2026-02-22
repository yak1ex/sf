import urllib.request
import re
import sys


METADATA_PATTERN = (
    r'<p>Version (?P<version>[\d.]+) \((?P<datetime>[-\d: ]+), '
    r'(?P<coq_version>[^)]+)\)(?:<br>\n\s*'
    r'Compatible with (?P<vst_version>.*))?</p>'
)
BASE_URL = "https://softwarefoundations.cis.upenn.edu"


def extract_latest_date():
    with open('README.md') as f:
        for line in f:
            if re.match(r'\|\|\d+/\d+/\d+\|', line):
                return line.split('|')[2]


def extract_volumes():
    with urllib.request.urlopen(BASE_URL) as response:
        content = response.read().decode('utf-8')
    return re.findall(r'<a href="([^/]*/index.html)">', content, )


def extract_info(latest_date, volume):
    with urllib.request.urlopen(f'{BASE_URL}/{volume}') as response:
        content = response.read().decode('utf-8')
    match = re.search(METADATA_PATTERN, content)
    if match:
        result = match.groupdict()
        result['datetime'] = result['datetime'].replace('-', '/')
        if result['datetime'].split(' ')[0] != latest_date:
            return result
        return None
    raise ValueError("Metadata not found in index.html")


def process(toml_path):
    result = {}
    latest_date = extract_latest_date()
    volumes = extract_volumes()
    for volume in volumes:
        info = extract_info(latest_date, volume)
        date = info['datetime'].split(' ')[0]
        if m := re.match(r'(.*)-current/index.html', volume):
            result.setdefault(date, []).append(f'{m.group(1)}="{info['version']}"')
    with open(toml_path, 'w') as f:
        for key in sorted(result.keys()):
            print(f'[{key}]', '\n'.join(result[key]), '', sep='\n', file=f)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python update_toml.py <path_to_toml>")
        sys.exit(1)
    process(sys.argv[1])
