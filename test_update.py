import base64
import hashlib
import os
import subprocess
import tempfile
import pytest
import pytest_mock
from contextlib import chdir
import update


# base64 encoded tgz file containing updated lf/index.html
# including Version 6.4 (2024-10-01 12:00, Coq 8.16
TGZ_B64 = """H4sIAAAAAAAAA+3SPU/DMBAGYM/9FTeCRONz/BGErCywsAO7UVIlUpqU2kjw73HaDjB0TJHgfRTp
oostX/Jm2EixNM4qa4Vhtq4q56rydeifCGW5qrTObSdYlVobQXbxybL3mMKeSIRcQuz6c+sepm3o
R3qO7T5eYq4LGTayH5v2o+jSdljojDlgZ8zZ/JWz3/LXOX+T7wTxQvP88M/z93Pu9cp3bWhqn/o0
tPVTGxM9zn+Fl8eOl4fnK/86NZ+57OqX/Bn6aSRXGLoquTRrxWtWpMo75hu6n97otlDu2stdXi9P
++TxtN9+aQAAAAAAAAAAAAAAAAAAAACAP+IL9poJVwAoAAA="""


# Mock network calls for download_tar
def mock_download_tar(url, dest_path):
    with open(dest_path, "wb") as f:
        f.write(base64.b64decode(TGZ_B64))


@pytest.fixture
def setup_index():
    with tempfile.TemporaryDirectory() as temp_dir:
        folder_path = os.path.join(temp_dir, "src", "lf")
        os.makedirs(folder_path)
        index_path = os.path.join(folder_path, "index.html")
        with open(index_path, "w") as f:
            f.write("""<html>
<head><title>Test Index</title></head>
<body>
<p>Version 6.3 (2024-06-01 12:00, Coq 8.15)</p>
</body>
</html>""")
        yield folder_path


@pytest.fixture
def setup_src():
    with tempfile.TemporaryDirectory() as temp_dir:
        src_path = os.path.join(temp_dir, "src")
        os.makedirs(src_path)
        os.mkdir(os.path.join(src_path, "lf"))
        os.mkdir(os.path.join(src_path, "plf"))
        with open(os.path.join(src_path, "lf", "index.html"), "w") as f:
            f.write("""<html>
<head><title>Test Index</title></head>
<body>
<p>Version 6.3 (2024-06-01 12:00, Coq 8.15)</p>
</body>
</html>""")
        with open(os.path.join(src_path, "plf", "index.html"), "w") as f:
            f.write("""<html>
<head><title>Test Index</title></head>
<body>
<p>Version 6.3 (2024-06-01 12:00, Coq 8.15)</p>
</body>
</html>""")
        subprocess.run(["git", "init"], cwd=temp_dir)
        subprocess.run(["git", "add", "."], cwd=temp_dir)
        subprocess.run(["git", "commit", "-m", "Initial commit"], cwd=temp_dir)
        yield src_path


@pytest.mark.slow
def test_download_tar():
    with tempfile.TemporaryDirectory() as temp_dir:
        dest_path = os.path.join(temp_dir, "lf-6.3.tgz")
        update.download_tar("https://softwarefoundations.cis.upenn.edu/lf-6.3/lf.tgz", dest_path)
        assert os.path.isfile(dest_path)
        # calculate sha256 of downloaded file
        sha256_hash = hashlib.sha256()
        with open(dest_path, "rb") as f:
            for byte_block in iter(lambda: f.read(4096), b""):
                sha256_hash.update(byte_block)
        assert sha256_hash.hexdigest() == "71d03081cedb34658be2090e63ad32bf602828e7197306e491090b161a0b81f3"


def test_download_tars(mocker):
    mocker.patch.object(update, 'download_tar', side_effect=mock_download_tar)
    data = {
        '2024-10-01': {
            'lf': '6.4',
            'plf': '6.4',
        },
        '2024-06-01': {
            'lf': '6.3',
            'plf': '6.3',
        },
    }
    with tempfile.TemporaryDirectory() as temp_dir:
        update.download_tars(data, temp_dir)
        for volume in ['lf', 'plf']:
            for version in ['6.4', '6.3']:
                tar_path = os.path.join(temp_dir, f"{volume}-{version}.tgz")
                assert os.path.isfile(tar_path)
                with open(tar_path, "rb") as f:
                    content = f.read()
                    assert content == base64.b64decode(TGZ_B64)


def test_process_toml(setup_src, mocker):
    mocker.patch.object(update, 'download_tar', side_effect=mock_download_tar)
    with tempfile.NamedTemporaryFile(delete=False) as temp_toml:
        temp_toml.write(b"""[2024-10-01]
lf = "6.4"
""")
        temp_toml_path = temp_toml.name
    with tempfile.TemporaryDirectory() as temp_tgz_dir:
        with chdir(os.path.join(setup_src, "..")):
            updates = update.process_toml(temp_toml_path, prefix=setup_src, tgz_dir=temp_tgz_dir)
            result = subprocess.run(["git", "log", "--stat"], cwd=os.path.join(setup_src, ".."), capture_output=True)

        lf_meta = update.extract_metadata(os.path.join(setup_src, "lf"))
        plf_meta = update.extract_metadata(os.path.join(setup_src, "plf"))

    assert updates == {
       '2024/10/01': {
           'lf': {
               'version': '6.4',
               'datetime': '2024/10/01 12:00',
               'coq_version': 'Coq 8.16',
               'prev_version': '6.3'
            },
       }
    }
    assert """Update sources (LF: v6.4).
    
    * LF:  v6.3   -> v6.4

 src/lf/index.html | 12 ++++++------
 1 file changed, 6 insertions(+), 6 deletions(-)""" in result.stdout.decode()
    assert lf_meta['version'] == '6.4'
    assert lf_meta['datetime'] == '2024/10/01 12:00'
    assert lf_meta['coq_version'] == 'Coq 8.16'
    assert plf_meta['version'] == '6.3'
    assert plf_meta['datetime'] == '2024/06/01 12:00'
    assert plf_meta['coq_version'] == 'Coq 8.15'


def test_extract_metadata(setup_index):
    folder_path = setup_index
    metadata = update.extract_metadata(folder_path)
    assert metadata['version'] == '6.3'
    assert metadata['datetime'] == '2024/06/01 12:00'
    assert metadata['coq_version'] == 'Coq 8.15'


def test_replace_folder(setup_index):
    folder_path = setup_index
    print(folder_path)
    tar_data = base64.b64decode(TGZ_B64)
    with tempfile.NamedTemporaryFile(delete=False) as temp_tar:
        temp_tar.write(tar_data)
        temp_tar_path = temp_tar.name
    update.replace_folder(temp_tar_path, folder_path)
    metadata = update.extract_metadata(folder_path)
    assert metadata['version'] == '6.4'
    assert metadata['datetime'] == '2024/10/01 12:00'
    assert metadata['coq_version'] == 'Coq 8.16'
    # Clean up temporary tar file
    os.remove(temp_tar_path)


def test_update_readme():
    # Setup a temporary README.md file
    with tempfile.TemporaryDirectory() as temp_dir:
        readme_path = os.path.join(temp_dir, "README.md")
        with open(readme_path, "w") as f:
            f.write("""||2023/7/6|
|-|-|
|1.Logical Foundations (lf)||
|2.Programming Language Foundations (plf)|[6.2](https://softwarefoundations.cis.upenn.edu/plf-6.2/index.html)<br>2023/07/06 15:52<br>Coq 8.15 or later|""")
        updates_all = {
            '2024/06/01': {
                'lf': {'version': '6.3', 'datetime': '2024/06/01 12:00', 'coq_version': 'Coq 8.16 or later'},
                'plf': {'version': '6.3', 'datetime': '2024/06/01 12:00', 'coq_version': 'Coq 8.16 or later'},
            },
            '2024/10/01': {
                'plf': {'version': '6.4', 'datetime': '2024/10/01 12:00', 'coq_version': 'Coq 8.16 or later'},
            },
        }
        update.update_readme(updates_all, readme_path=readme_path)
        with open(readme_path, "r") as f:
            lines = f.readlines()
            assert "||2024/10/01|2024/06/01|2023/7/6|\n" == lines[0]
            assert "|-|-|-|-|\n" == lines[1]
            assert "|1.Logical Foundations (lf)||[6.3](https://softwarefoundations.cis.upenn.edu/lf-6.3/index.html)<br>2024/06/01 12:00<br>Coq 8.16 or later||\n" == lines[2]
            assert "|2.Programming Language Foundations (plf)|[6.4](https://softwarefoundations.cis.upenn.edu/plf-6.4/index.html)<br>2024/10/01 12:00<br>Coq 8.16 or later|[6.3](https://softwarefoundations.cis.upenn.edu/plf-6.3/index.html)<br>2024/06/01 12:00<br>Coq 8.16 or later|[6.2](https://softwarefoundations.cis.upenn.edu/plf-6.2/index.html)<br>2023/07/06 15:52<br>Coq 8.15 or later|\n" == lines[3]


@pytest.mark.parametrize(
    ["updates", "expected"],
    [
        pytest.param(
            {
                'lf': {'version': '6.3', 'prev_version': '6.2'},
                'plf': {'version': '6.3', 'prev_version': '6.2'},
            },
            """Update sources (LF: v6.3 and PLF: v6.3).

* LF:  v6.2   -> v6.3
* PLF: v6.2   -> v6.3
"""
        ),
        pytest.param(
            {
                'vc': {'version': '1.2.2', 'prev_version': '1.2.1'},
            },
            """Update sources (VC: v1.2.2).

* VC:  v1.2.1 -> v1.2.2
"""
        ),
        pytest.param(
            {
                'lf': {'version': '6.3', 'prev_version': '6.2'},
                'plf': {'version': '6.3', 'prev_version': '6.2'},
                'vc': {'version': '1.2.2', 'prev_version': '1.2.1'},
            },
            """Update sources (LF: v6.3, PLF: v6.3 and VC: v1.2.2).

* LF:  v6.2   -> v6.3
* PLF: v6.2   -> v6.3
* VC:  v1.2.1 -> v1.2.2
"""
        ),
    ]
)
def test_create_commit_message(updates, expected):
    actual = update.create_commit_message(updates)
    assert actual == expected
