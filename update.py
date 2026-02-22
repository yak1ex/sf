import os
import re
import subprocess
import shutil
import sys
import tarfile
import urllib.request
if sys.version_info >= (3, 12):
    import tomllib
    TOML_MODE = 'rb'
    EXTRACT_ALL_KWARGS = {'filter': 'data'}
elif sys.version_info >= (3, 11):
    import tomllib
    TOML_MODE = 'rb'
    EXTRACT_ALL_KWARGS = {}
else:
    import toml as tomllib
    TOML_MODE = 'r'
    EXTRACT_ALL_KWARGS = {}

# TODO: You need to add a line for the new volume in README.md manually.

"""
Toml data example:

[yyyy-mm-dd]
lf=6.3
plf=6.3
qc=1.5.3

[yyyy-mm-dd]
vfa=6.4
vc=6.4
"""


METADATA_PATTERN = (
    r'<p>Version (?P<version>[\d.]+) \((?P<datetime>[-\d: ]+), '
    r'(?P<coq_version>[^)]+)\)(?:<br>\n\s*'
    r'Compatible with (?P<vst_version>.*))?</p>'
)
BASE_URL = "https://softwarefoundations.cis.upenn.edu"


def download_tar(url, dest_path):
    """Download a tar file from the specified URL to the destination path

    Args:
        url (str): The URL of the tar file to download
        dest_path (str): The destination path to save the downloaded tar file
    """
    with urllib.request.urlopen(url) as response, open(dest_path, 'wb') as out_file:
        shutil.copyfileobj(response, out_file)


def download_tars(data, dest_dir):
    """Download multiple tar files based on the provided data dictionary

    Args:
        data (dict): A dictionary where keys are volume names and values are version strings
        dest_dir (str): The destination directory to save the downloaded tar files
    """
    for _, update in data.items():
        for volume, version in update.items():
            tar_filename = f"{volume}-{version}.tgz"
            url = f"{BASE_URL}/{volume}-{version}/{volume}.tgz"
            dest_file_path = os.path.join(dest_dir, tar_filename)
            download_tar(url, dest_file_path)


def replace_folder(tar_path, folder_path):
    """Clear the specified folder content and extract the tar content into it

    Args:
        tar_path (str): A path to tar file, which must contain the leaf folder of folder_path
        folder_path (str): A path to the folder to be replaced
    """
    if os.path.exists(folder_path):
        shutil.rmtree(folder_path)
    os.makedirs(folder_path, exist_ok=True)
    with tarfile.open(tar_path, "r:*") as tar:
        tar.extractall(path=os.path.join(folder_path, ".."), **EXTRACT_ALL_KWARGS)


def extract_metadata(folder_path):
    """Extract metadata from index in the specified folder

    Args:
        folder_path (str): A path to the folder
    """
    index_path = os.path.join(folder_path, "index.html")
    with open(index_path, "r", encoding="utf-8") as f:
        content = f.read()
        match = re.search(METADATA_PATTERN, content)
        if match:
            result = match.groupdict()
            result['datetime'] = result['datetime'].replace('-', '/')
            return result
        raise ValueError("Metadata not found in index.html")


def update_readme(updates_all, readme_path="README.md"):
    """Update README.md with the provided updates information

    Args:
        updates (dict): A dictionary containing update information
    """
    dates = list(updates_all.keys())
    dates.reverse()

    with open(readme_path, "r", encoding="utf-8") as f:
        lines = f.readlines()

    with open(readme_path, "w", encoding="utf-8") as f:
        row = 0
        for line in lines:
            if line[0] == '|':  # Table row
                row += 1
                if row == 1:
                    # If the first row, dates are prepended
                    new_line = '|'
                    for date in dates:
                        new_line += f"|{date}"
                    new_line += line[1:]
                    f.write(new_line)
                elif row == 2:
                    # If the second row, separator is prepended
                    new_line = '|-'
                    for _ in dates:
                        new_line += "|-"
                    new_line += line[2:]
                    f.write(new_line)
                else:
                    # Other rows are updated with new info
                    parts = line.strip().split('|')
                    match = re.search(r'\(([a-z]+)\)', parts[1])
                    volume = match.group(1)
                    new_line = f"|{parts[1]}"
                    for date in dates:
                        if volume in updates_all[date]:
                            meta = updates_all[date][volume]
                            new_line += (
                                f"|[{meta['version']}]({BASE_URL}/{volume}-{meta['version']}/index.html)<br>"
                                f"{meta['datetime']}<br>{meta['coq_version']}"
                                f"{(' with ' + meta['vst_version']) if meta.get('vst_version') else ''}"
                            )
                        else:
                            new_line += "|"
                    new_line += '|' + '|'.join(parts[2:]) + '\n'
                    f.write(new_line)
            else:
                f.write(line)


def create_commit_message(updates):
    """Create a commit message based on the provided updates information"""
    message = "Update sources ("
    for volume in updates.keys():
        if volume != list(updates.keys())[0]:
            if volume == list(updates.keys())[-1]:
                message += " and "
            else:
                message += ", "
        message += f"{volume.upper()}: v{updates[volume]['version']}"
    message += ").\n\n"

    for volume in updates.keys():
        meta = updates[volume]
        message += f"* {volume.upper()+':':4} {'v' if meta['prev_version'] else ''}{meta['prev_version']:5} -> v{meta['version']}\n"

    return message


def process_toml(toml_path, prefix='src', tgz_dir='.'):
    with open(toml_path, TOML_MODE) as f:
        data = tomllib.load(f)

    download_tars(data, tgz_dir)

    updates = {}
    for date in data.keys():
        datestr = date.replace('-', '/')
        for volume in data[date].keys():
            tar_file = f"{volume}-{data[date][volume]}.tgz"
            target_path = os.path.join(prefix, volume)
            if os.path.exists(target_path):
                prev_meta = extract_metadata(target_path)
            else:
                prev_meta = {'version': ''}
            replace_folder(os.path.join(tgz_dir, tar_file), target_path)
            update = updates.setdefault(datestr, {})
            update[volume] = extract_metadata(target_path)
            update[volume]['prev_version'] = prev_meta['version']
            subprocess.run(["git", "add", os.path.join(prefix, volume)])
        subprocess.run(["git", "commit", "-m", create_commit_message(updates[datestr])])

    return updates


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python update.py <path_to_toml>")
        sys.exit(1)
    updates = process_toml(sys.argv[1])
    update_readme(updates)
