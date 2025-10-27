import os
import re
import subprocess
import shutil
import sys
import tarfile
import tomllib


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


METADATA_PATTERN = r'<p>Version (?P<version>[\d.]+) \((?P<datetime>[-\d: ]+), (?P<coq_version>[^)]+)\)</p>'
BASE_URL = "https://softwarefoundations.cis.upenn.edu/"


def replace_folder(tar_path, folder_path):
    """Clear the specified folder content and extract the tar content into it

    Args:
        tar_path (str): A path to tar file, which must contain the leaf folder of folder_path
        folder_path (str): A path to the folder to be replaced
    """
    shutil.rmtree(folder_path)
    os.makedirs(folder_path, exist_ok=True)
    with tarfile.open(tar_path, "r:*") as tar:
        tar.extractall(path=os.path.join(folder_path, ".."), filter='data')


def extract_metadata(folder_path):
    """Extract metadata from index in the specified folder

    Args:
        folder_path (str): A path to the folder
    """
    index_path = os.path.join(folder_path, "index.html")
    with open(index_path, "r", encoding="utf-8") as f:
        for line in f:
            match = re.search(METADATA_PATTERN, line)
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
                            new_line += f"|[{meta['version']}]({BASE_URL}{volume}-{meta['version']}/index.html)<br>" \
                                        f"{meta['datetime']}<br>{meta['coq_version']}"
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
        message += f"* {volume.upper()+':':4} v{meta['prev_version']:5} -> v{meta['version']}\n"

    return message


def process_toml(toml_path, prefix='src', tgz_dir='.'):
    with open(toml_path, "rb") as f:
        data = tomllib.load(f)

    updates = {}
    for date in data.keys():
        datestr = date.replace('-', '/')
        for volume in data[date].keys():
            tar_file = f"{volume}-{data[date][volume]}.tgz"
            target_path = os.path.join(prefix, volume)
            prev_meta = extract_metadata(target_path)
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
