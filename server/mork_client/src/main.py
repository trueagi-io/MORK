import httpx
from httpx import URL
from typing import Optional
import os
from urllib.parse import quote

class MorkClient:
    """
    MorkClient is a client for the MORK server.
    """

    def __init__(self, url: Optional[str| URL] = os.environ.get("MORK_URL")):
        if url is None:
            raise ValueError(
                "MORK_URL environment variable is not set. Please set it using \
                `export MORK_URL=http://localhost:8000/`."
            )

        if isinstance(url, URL):
            self.url = url
            return

        if isinstance(url, str):
            url = url.strip()

        self.url: URL = URL(url)

    async def _request(self, method: str = "GET", path: str = "", **kwargs):
        """request mork api, *args and **kwargs are valid httpx.request arguments"""

        assert path.startswith("/"), "Path must start with /"

        url = self.url.copy_with(path=path)

        async with httpx.AsyncClient() as client:
            return await client.request(method, url, **kwargs)

    async def _mork_to_path(self, mork_path: str):
        """changes mork code to valid path parameters"""

        lines = mork_path.split('\n')
        lines = [line.strip() for line in lines]
        lines = [line for line in lines if line != ""]  # remove empty lines
        path = "/".join(lines)

        return path

    async def busywait(self, timeout: int = 2000, **kwargs):
        await self._request(method="GET", path=f"/busywait/{timeout}", **kwargs)

    async def clear(self, expr: str, **kwargs):
        path = quote(expr.strip())

        return await self._request(
            method="GET",
            path=f"/clear/{path}",
            **kwargs
        )

    async def count(self, expr: str, **kwargs):
        path = quote(expr.strip())

        return await self._request(
            method="GET",
            path=f"/count/{path}",
            **kwargs
        )

    async def export(self, expr: str, **kwargs):
        path = quote(await self._mork_to_path(expr))

        return await self._request(
            method="GET",
            path=f"/export/{path}",
            **kwargs
        )

    async def import_(self, expr: str, **kwargs):
        path = quote(await self._mork_to_path(expr))

        print("path: ", path)
        return await self._request(
            method="GET",
            path=f"/import/{path}",
            **kwargs
        )

    async def status(self, expr: str, **kwargs):
        path = quote(expr.strip())

        return await self._request(
            method="GET",
            path=f"/status/{path}",
            **kwargs
        )

    async def stop(self, **kwargs):
        kwargs["wait_for_idle"] = ""  # must be set
        return await self._request(
            method="GET",
            path="/stop/",
            **kwargs
        )

    async def upload(self, expr: str, payload: str, **kwargs):

        path = quote(await self._mork_to_path(expr))

        if kwargs.get("headers") is None:
            kwargs["headers"] = {
                "Content-Type": "text/plain"
            }
        else: 
            kwargs["headers"]["Content-Type"] = "text/plain"
            kwargs["headers"]["content-type"] = "text/plain"

        return await self._request(
            method="POST",
            path=f"/upload/{path}",
            content=payload,
            **kwargs
        )

    async def transform(self, expr: str, payload: str, **kwargs):
        path = quote(await self._mork_to_path(expr))

        if kwargs.get("headers") is None:
            kwargs["headers"] = {
                "Content-Type": "text/plain"
            }
        else: 
            kwargs["headers"]["Content-Type"] = "text/plain"
            kwargs["headers"]["content-type"] = "text/plain"


        return await self._request(
            method="POST",
            path=f"/transform/{path}",
            content=payload,
            **kwargs
        )


    # apis assumed to exist

    async def metta_thread(self):
        print("Not implemented")

    async def metta_thread_suspend(self):
        print("Not implemented")

    async def transform_multi_multi(self):
        print("Not implemented")


